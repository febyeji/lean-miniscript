import LeanMiniscript.Extraction.BitcoinCoreFixtures

open LeanMiniscript.Script

namespace LeanMiniscript.Extraction

/-! Verbatim signature-encoding rejection rows from the pinned v31.1 file.
    Rows requiring a real verifier are retained as explicit unsupported cases.
    BIP66 example 7 (row 7) is explicitly excluded; the other 15 rows must
    match with both accepting and rejecting oracles. -/

private def pinnedEncodingRows : String := "[
  [
    \"0 0x47 0x304402205451ce65ad844dbb978b8bdedf5082e33b43cae8279c30f2c74d9e9ee49a94f802203fe95a7ccf74da7a232ee523ef4a53cb4d14bdd16289680cdb97a63819b8f42f01 0x46 0x304402205451ce65ad844dbb978b8bdedf5082e33b43cae8279c30f2c74d9e9ee49a94f802203fe95a7ccf74da7a232ee523ef4a53cb4d14bdd16289680cdb97a63819b8f42f\",
    \"2 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 3 CHECKMULTISIG\",
    \"P2SH,STRICTENC\",
    \"SIG_DER\",
    \"2-of-3 with one valid and one invalid signature due to parse error, nSigs > validSigs (STRICTENC enabled).\"
  ],
  [
    \"0 0x47 0x304402205451ce65ad844dbb978b8bdedf5082e33b43cae8279c30f2c74d9e9ee49a94f802203fe95a7ccf74da7a232ee523ef4a53cb4d14bdd16289680cdb97a63819b8f42f01 0x46 0x304402205451ce65ad844dbb978b8bdedf5082e33b43cae8279c30f2c74d9e9ee49a94f802203fe95a7ccf74da7a232ee523ef4a53cb4d14bdd16289680cdb97a63819b8f42f\",
    \"2 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 0x21 0x02a673638cb9587cb68ea08dbef685c6f2d2a751a8b3c6f2a7e9a4999e6e4bfaf5 3 CHECKMULTISIG\",
    \"P2SH,DERSIG\",
    \"SIG_DER\",
    \"2-of-3 with one valid and one invalid signature due to parse error, nSigs > validSigs (DERSIG enabled).\"
  ],
  [
    \"0x47 0x304402200060558477337b9022e70534f1fea71a318caf836812465a2509931c5e7c4987022078ec32bd50ac9e03a349ba953dfd9fe1c8d2dd8bdb1d38ddca844d3d5c78c11801\",
    \"0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"P2PK with too much R padding\"
  ],
  [
    \"0x48 0x304502202de8c03fc525285c9c535631019a5f2af7c6454fa9eb392a3756a4917c420edd02210046130bf2baf7cfc065067c8b9e33a066d9c15edcea9feb0ca2d233e3597925b401\",
    \"0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"P2PK with too much S padding\"
  ],
  [
    \"0x47 0x30440220d7a0417c3f6d1a15094d1cf2a3378ca0503eb8a57630953a9e2987e21ddd0a6502207a6266d686c99090920249991d3d42065b6d43eb70187b219c0db82e4f94d1a201\",
    \"0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"P2PK with too little R padding\"
  ],
  [
    \"0x47 0x30440220d7a0417c3f6d1a15094d1cf2a3378ca0503eb8a57630953a9e2987e21ddd0a6502207a6266d686c99090920249991d3d42065b6d43eb70187b219c0db82e4f94d1a201\",
    \"0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"BIP66 example 1, with DERSIG\"
  ],
  [
    \"1\",
    \"0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"BIP66 example 5, with DERSIG\"
  ],
  [
    \"0 0x47 0x30440220cae00b1444babfbf6071b0ba8707f6bd373da3df494d6e74119b0430c5db810502205d5231b8c5939c8ff0c82242656d6e06edb073d42af336c99fe8837c36ea39d501 0x47 0x3044022027c2714269ca5aeecc4d70edc88ba5ee0e3da4986e9216028f489ab4f1b8efce022022bd545b4951215267e4c5ceabd4c5350331b2e4a0b6494c56f361fa5a57a1a201\",
    \"2 0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 0x21 0x03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640 2 CHECKMULTISIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"BIP66 example 7, with DERSIG\"
  ],
  [
    \"0 0 0x47 0x3044022081aa9d436f2154e8b6d600516db03d78de71df685b585a9807ead4210bd883490220534bb6bdf318a419ac0749660b60e78d17d515558ef369bf872eff405b676b2e01\",
    \"2 0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 0x21 0x03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640 2 CHECKMULTISIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"BIP66 example 9, with DERSIG\"
  ],
  [
    \"0x48 0x304402203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c022054e1c258c2981cdfba5df1f46661fb6541c44f77ca0092f3600331abfffb12510101\",
    \"0x21 0x03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640 CHECKSIG\",
    \"DERSIG\",
    \"SIG_DER\",
    \"P2PK with multi-byte hashtype, with DERSIG\"
  ],
  [
    \"0x48 0x304502203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c022100ab1e3da73d67e32045a20e0b999e049978ea8d6ee5480d485fcf2ce0d03b2ef001\",
    \"0x21 0x03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640 CHECKSIG\",
    \"LOW_S\",
    \"SIG_HIGH_S\",
    \"P2PK with high S\"
  ],
  [
    \"0x47 0x3044022057292e2d4dfe775becdd0a9e6547997c728cdf35390f6a017da56d654d374e4902206b643be2fc53763b4e284845bfea2c597d2dc7759941dce937636c9d341b71ed01\",
    \"0x41 0x0679be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 CHECKSIG\",
    \"STRICTENC\",
    \"PUBKEYTYPE\",
    \"P2PK with hybrid pubkey\"
  ],
  [
    \"0x00\",
    \"0x21 0x0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 CHECKSIG\",
    \"STRICTENC\",
    \"PUBKEYTYPE\",
    \"P2PK with invalid length for uncompressed key\"
  ],
  [
    \"0x00\",
    \"0x41 0x0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 CHECKSIG\",
    \"STRICTENC\",
    \"PUBKEYTYPE\",
    \"P2PK with invalid length for compressed key\"
  ],
  [
    \"0 0x47 0x3044022079c7824d6c868e0e1a273484e28c2654a27d043c8a27f49f52cb72efed0759090220452bbbf7089574fa082095a4fc1b3a16bafcf97a3a34d745fafc922cce66b27201\",
    \"1 0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 0x41 0x0679be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 2 CHECKMULTISIG\",
    \"STRICTENC\",
    \"PUBKEYTYPE\",
    \"1-of-2 with the first 1 hybrid pubkey\"
  ],
  [
    \"0x47 0x304402206177d513ec2cda444c021a1f4f656fc4c72ba108ae063e157eb86dc3575784940220666fc66702815d0e5413bb9b1df22aed44f5f1efb8b99d41dd5dc9a5be6d205205\",
    \"0x41 0x048282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f5150811f8a8098557dfe45e8256e830b60ace62d613ac2f7b17bed31b6eaff6e26caf CHECKSIG\",
    \"STRICTENC\",
    \"SIG_HASHTYPE\",
    \"P2PK with undefined hashtype\"
  ]
]"

private def comparesPinnedEncodingRows : Bool :=
  match parseCoreScriptTests pinnedEncodingRows with
  | .error _ => false
  | .ok rows => rows.zipIdx.all fun (row, index) =>
      match row with
      | .comment _ => false
      | .test test =>
          match prepareCoreFixture test with
          | .error .signatureOpcode => index == 7
          | .error _ => false
          | .ok fixture =>
              let rejecting := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
              let accepting := CryptoOracle.pureLeanHashes (fun _ _ _ => true)
              index != 7 && (runCoreFixture rejecting fixture).coreTag == test.expectedError &&
                (runCoreFixture accepting fixture).coreTag == test.expectedError

example : comparesPinnedEncodingRows = true := by native_decide

/-- A later encoding error cannot justify admitting a row if matching must
    first consult a verifier. With two signatures and two keys, a rejected
    first match can stop before the malformed second signature. -/
private def excludesVerifierDependentEncoding : Bool :=
  let test : CoreScriptTest := {
    witness := none
    scriptSigSource := "0 1 0x09 0x300602010102010101"
    scriptPubKeySource := "2 0x21 0x020101010101010101010101010101010101010101010101010101010101010101 0x21 0x020101010101010101010101010101010101010101010101010101010101010101 2 CHECKMULTISIG"
    flagSource := "STRICTENC"
    expectedError := "SIG_DER"
    comments := [] }
  match prepareCoreFixture test with
  | .error .signatureOpcode => true
  | _ => false

example : excludesVerifierDependentEncoding = true := by native_decide

/-- Admission depends on the verifier boundary, so a wrong expected tag is
    exposed as a mismatch instead of being silently filtered out. -/
private def exposesWrongEncodingTag : Bool :=
  let test : CoreScriptTest := {
    witness := none, scriptSigSource := "1 0", scriptPubKeySource := "CHECKSIG"
    flagSource := "STRICTENC", expectedError := "OK", comments := [] }
  match checkCoreFixture (CryptoOracle.pureLeanHashes (fun _ _ _ => false)) test with
  | .ok false => true
  | _ => false

example : exposesWrongEncodingTag = true := by native_decide

end LeanMiniscript.Extraction
