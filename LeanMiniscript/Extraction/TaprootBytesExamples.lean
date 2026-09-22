import LeanMiniscript.Extraction.TaprootBytes
import LeanMiniscript.Bitcoin.TaprootSighashExamples

namespace LeanMiniscript.Extraction

open Script Bitcoin

local instance canonicalTapscriptExceptDecidableEq
    {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := by
  intro first second
  cases first <;> cases second <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def flip (bytes : ByteArray) (index : Nat) : ByteArray :=
  ⟨bytes.data.set! index (bytes[index]! ^^^ 1)⟩

-- Reuse the public test-key vectors reproduced by
-- scripts/generate_taproot_control_fixtures.py for TaprootExamples.lean.
private def key := hex "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9"
private def control := hex "c02f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"
private def program := hex "5120bf6cf4c0026f57cab510d2014e34e8bad549e5370ed343b1e333fc5a3b066413"
private def signature := hex "8c05c0ee555979c2de9025bc3664cb322783a198339d3d458c3d73b4364f235444e98c7661e6010ac1ffbb07a2c68f87a407ac4f089a5dd1ff88574524a53a48"
private def scriptBytes := hex "20" ++ key ++ hex "ac"
private def prevouts := sighashFixtureSpentOutputs.modify 0
  (fun output => { output with scriptPubKey := program })
private def fullWitness := [signature, scriptBytes, control]
private def annexWitness := [hex "35cc69fbeb571616eff22e2372add7bc7f9028744431757baeb6dd257a41e17a6f2d66a4bf532402c964fdee6728664cffb963159121a76ea648dbb232677ccd", scriptBytes, control, hex "500102"]

private def verify (witness : List ByteArray) (flags : ScriptFlags := {})
    (tx : Transaction := sighashFixtureTransaction) (spent : Array TxOutput := prevouts) :
    Except CanonicalTapscriptVerificationError Nat :=
  verifyCanonicalTapscriptTransaction CryptoOracle.pureLeanSchnorr witness flags tx spent 0

-- Real transaction-derived Schnorr verification, with no AST argument.
example : verify fullWitness = .ok (initialValidationWeight fullWitness - 50) := by native_decide
example : verify annexWitness = .ok (initialValidationWeight annexWitness - 50) := by native_decide
example : verify [flip signature 40, scriptBytes, control] =
    .error (.script .schnorrSig) := by native_decide
example : verify fullWitness {} { sighashFixtureTransaction with
    locktime := sighashFixtureTransaction.locktime + 1 } =
    .error (.script .schnorrSig) := by native_decide
example : verify (fullWitness ++ [hex "500102"]) =
    .error (.script .schnorrSig) := by native_decide
example : verify [ByteArray.empty, scriptBytes, control] =
    .error (.script .evalFalse) := by native_decide
example : verify (ByteArray.empty :: fullWitness) =
    .error (.script .cleanStack) := by native_decide
example : verify fullWitness { minimalData := false } =
    .error (.script .tapscriptFlags) := by native_decide

example : verify [] = .error (.setup .emptyWitness) := by native_decide
example : verify [signature] = .error (.setup .keyPathUnsupported) := by native_decide
example : verify fullWitness {} sighashFixtureTransaction #[] =
    .error (.setup (.context .spentOutputCount)) := by native_decide
example : verify [signature, scriptBytes, flip control 0] =
    .error (.setup (.control .commitmentMismatch)) := by native_decide
example : verify [signature, scriptBytes ++ hex "00", control] =
    .error (.setup (.control .commitmentMismatch)) := by native_decide

private def oversized : ByteArray := ⟨Array.replicate 521 1⟩
example : verify [oversized, scriptBytes, control] =
    .error (.script .pushSize) := by native_decide
example : verify (List.replicate 1001 oversized ++ [scriptBytes, control]) =
    .error (.script .stackSize) := by native_decide
example : verify (List.replicate 999 ByteArray.empty ++ fullWitness) =
    .error (.script .stackSize) := by native_decide
example : verify [oversized, scriptBytes, flip control 0] { minimalData := false } =
    .error (.setup (.control .commitmentMismatch)) := by native_decide

-- Construct valid commitments for synthetic decoding/support-boundary cases.
-- These are model regressions; the real signature fixtures above are externally
-- generated. The outer Except ensures commitment construction must succeed.
private def encodeBE32 (value : Nat) : ByteArray :=
  ⟨((List.range 32).map (fun i => UInt8.ofNat (value / 256 ^ (31 - i) % 256))).toArray⟩

private def verifyBytes (bytes : ByteArray) (flags : ScriptFlags := {})
    (breakCommitment : Bool := false) :
    Except TaprootControlError (Except CanonicalTapscriptVerificationError Nat) := do
  let internal := control.extract 1 33
  let (x, y) ← taprootTweakPoint internal
    (taggedHash "TapTweak" (internal ++ tapleafHash bytes 0xc0))
  let controlByte := UInt8.ofNat (0xc0 + y % 2)
  let witnessControl := ⟨#[controlByte]⟩ ++ internal
  let spent := prevouts.modify 0 (fun output =>
    { output with scriptPubKey := hex "5120" ++ encodeBE32 x })
  let witness := [bytes, if breakCommitment then flip witnessControl 0 else witnessControl]
  return verify witness flags sighashFixtureTransaction spent

example : verifyBytes (hex "51") = .ok (.ok 87) := by native_decide
example : verifyBytes (hex "00") = .ok (.error (.script .evalFalse)) := by native_decide
example : verifyBytes (hex "5151") = .ok (.error (.script .cleanStack)) := by native_decide
example : verifyBytes (hex "4c") =
    .ok (.error (.decode (.truncatedPushLength 0 1 0))) := by native_decide
example : verifyBytes (hex "02ff") =
    .ok (.error (.decode (.truncatedPushData 0 2 1))) := by native_decide
example : verifyBytes (hex "4d01") =
    .ok (.error (.decode (.truncatedPushLength 0 2 1))) := by native_decide
-- OP_SUCCESSx is reported outside the modeled opcode subset.
example : verifyBytes (hex "50") =
    .ok (.error (.decode (.unsupportedOpcode 0 0x50))) := by native_decide
example : verifyBytes (hex "51ff") =
    .ok (.error (.decode (.unsupportedOpcode 1 0xff))) := by native_decide

-- Non-canonical pushes remain support-boundary errors even in inactive paths
-- or when the caller disables minimalData.
example : ["0101", "4c0101", "4d010001", "4e0100000001", "00634c01016851"].all
    (fun bytes => decide (verifyBytes (hex bytes) = .ok (.error .nonCanonicalScript))) = true := by
  native_decide
example : verifyBytes (hex "4c0101") { minimalData := false } =
    .ok (.error .nonCanonicalScript) := by native_decide

-- Setup errors precede decoding, canonicality, and flag-contract failures.
example : verifyBytes (hex "4c") { minimalData := false } true =
    .ok (.error (.setup (.control .commitmentMismatch))) := by native_decide
example : verifyBytes (hex "4c0101") {} true =
    .ok (.error (.setup (.control .commitmentMismatch))) := by native_decide

end LeanMiniscript.Extraction
