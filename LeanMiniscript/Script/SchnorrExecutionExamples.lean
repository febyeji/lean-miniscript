import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Extraction.RefInterp

namespace LeanMiniscript.Script
open LeanMiniscript.Bitcoin
private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def key := hex "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9"
private def script : Script := [.pushData key, .op .OP_CHECKSIG]
private def witness (signature : ByteArray) : TapscriptWitness :=
  { arguments := [signature], scriptBytes := hex "20" ++ key ++ hex "ac",
    controlBlock := ⟨Array.replicate 33 0xc0⟩ }
private def success : WeightedResult → Bool
  | .success [top] _ _ => top.data == trueElement.data
  | _ => false
private def errorIs (expected : ScriptError) : WeightedResult → Bool
  | .failure error => error == expected
  | _ => false
private def run (w : TapscriptWitness) (tx : Transaction := sighashFixtureTransaction) : WeightedResult :=
  LeanMiniscript.Extraction.execTapscriptTransaction CryptoOracle.pureLeanSchnorr script w {}
    tx sighashFixtureSpentOutputs 0

-- Independent Core hashing plus the pinned BIP340 reference signer.
private def signatures : List (UInt8 × String) := [
  (0, "51679e11304c0f74bba084a23d415b849f6dfece1e347285e142508d15d14e9abd0c6f05473ba384e7b4dab8006647fd5d7787a6dd39c82e97053a4ade595b8b"),
  (1, "080fca2cf5059a1aeb3d59248c4b85ff25a16fb4cc98ebb2ddf4d704068e3a6bc785d71904dc758495f928ca6485570a4743dd0c833e315190f3d8549b504ebc01"),
  (2, "f0843ec4c4c733c403b2957715a97b6aef275e906a4d97baaaef71fe1f18135ad43ac94d09d59c87b168c9fb1d626c206c472cbd5fd7c328d3d7ec5c5cb8ee0802"),
  (3, "64e91d46f57f54f29c8e3c53fcd6bebfbb8ecf3101547d94b673b2432edde25555de9a21e28fb5cf8d035f9c49283ca34428e963ab5ed78d79480070688029bf03"),
  (129, "59c7b7fc8ef6289b64645bdb04e5ee013fc4b6a1ff713788eeade1a2d7e424fc1fe219cb3f43ce14d3592bddaa4bb3544ef3a47270cae41e446c951a6465bb2381"),
  (130, "0ae2596d7518f0fa9a771b465fc7d6e4aee28a5945f69112d5736b115fa7f83ce846badef655c57aa8027eab0ae495ba2ca7d2d5b92059d9dfdee36ba072310082"),
  (131, "72a2d6cf1ec9cd259a2a8ece039295e6159ebd793067a4abbf73433669b27b5d7bd0601891927bc6da5f6b713716ea5d2f2315f925e3293f0a17a78c036c88bb83"),
]
example : signatures.all (fun (_, sig) => success (run (witness (hex sig)))) = true := by native_decide
private def defaultSig := hex "51679e11304c0f74bba084a23d415b849f6dfece1e347285e142508d15d14e9abd0c6f05473ba384e7b4dab8006647fd5d7787a6dd39c82e97053a4ade595b8b"
example : success (run { witness (hex "8e73ae0923690e1b63d4aa937862010f26738ac0f53e7aa79884bca4d65b5ae6a5546016eb19dc8ebd69c57ed3e932de076c0a3d7459cf2565aba7d356d11646") with annex := some (hex "500102") }) = true := by native_decide
example : success (LeanMiniscript.Extraction.execTapscriptTransaction CryptoOracle.pureLeanSchnorr
  [.pushNum 0, .pushData key, .op .OP_CHECKSIGADD]
  { arguments := [hex "842e9a5aef654e1dd21c9005c9759cdab51eae3bb4507f4e0e06c7c24f676c2890306848165cdf8be771de428b9f1d92dce3416ff263b9f6114b234c78528f6c"], scriptBytes := hex "0020f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9ba", controlBlock := (witness defaultSig).controlBlock }
  {} sighashFixtureTransaction sighashFixtureSpentOutputs 0) = true := by native_decide

-- Mutating the signature, committed transaction, or annex rejects real crypto.
private def corrupted : ByteArray := ⟨defaultSig.data.set! 40 (defaultSig[40]! ^^^ 1)⟩
example : errorIs .schnorrSig (run (witness corrupted)) = true := by native_decide
example : errorIs .schnorrSig (run (witness defaultSig)
  { sighashFixtureTransaction with locktime := sighashFixtureTransaction.locktime + 1 }) = true := by native_decide
example : errorIs .schnorrSig (run { witness defaultSig with annex := some (hex "500102") }) = true := by native_decide
example : errorIs .schnorrSigHashType (run (witness (defaultSig ++ hex "00"))) = true := by native_decide
example : errorIs .schnorrSigSize (run (witness (defaultSig.extract 0 63))) = true := by native_decide
example : (match run (witness ByteArray.empty) with
  | .success [top] _ _ => top.data == falseElement.data
  | _ => false) = true := by native_decide
-- Standalone BIP340 rejects 65 bytes; Script strips its valid explicit type byte.
example : signatures.all (fun (mode, sig) => mode == 0 ||
  !Schnorr.verify (hex sig) key ByteArray.empty) = true := by native_decide
-- ECDSA remains explicitly supplied, with rejection as the default.
example : CryptoOracle.pureLeanSchnorr.checkSig defaultSig key ByteArray.empty = false := by native_decide
end LeanMiniscript.Script
