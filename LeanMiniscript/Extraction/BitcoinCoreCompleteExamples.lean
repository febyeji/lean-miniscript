import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

/-! Regression rows copied verbatim from the pinned Core fixture. These cover
all former exclusion categories, including the five generated Taproot scripts. -/

private def completeBoundaryIndices : List Nat := [50, 223, 399, 458, 580, 918, 1019, 1063, 1109, 1111, 1114, 1134, 1181, 1258, 1259, 1260, 1261, 1262]

private def completeBoundaryFixtures : String := r####"
[
  [
    "'' 1",
    "IF SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ELSE ELSE SHA1 ENDIF 0x14 0x68ca4fec736264c13b859bac43d5173df6871682 EQUAL",
    "P2SH,STRICTENC",
    "OK"
  ],
  [
    "1",
    "NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4 NOP5 NOP6 NOP7 NOP8 NOP9 NOP10 1 EQUAL",
    "P2SH,STRICTENC",
    "OK"
  ],
  [
    "NOP",
    "CHECKSEQUENCEVERIFY 1",
    "P2SH,STRICTENC",
    "OK"
  ],
  [
    "0 0x01 1",
    "HASH160 0x14 0xda1745e9b549bd0bfa1a569971c77eba30cd5a4b EQUAL",
    "P2SH,STRICTENC",
    "OK",
    "Very basic P2SH"
  ],
  [
    "0",
    "0x21 0x02865c40293a680cb9c020e7b1e106d8c1916d3cef99aa431a56d253e69256dac0 CHECKSIG NOT",
    "STRICTENC",
    "OK"
  ],
  [
    "NOP 0x01 1",
    "HASH160 0x14 0xda1745e9b549bd0bfa1a569971c77eba30cd5a4b EQUAL",
    "P2SH,STRICTENC",
    "SIG_PUSHONLY",
    "Tests for Script.IsPushOnly()"
  ],
  [
    [
      "00",
      0.0
    ],
    "",
    "0 0x206e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
    "P2SH,WITNESS",
    "EVAL_FALSE",
    "Invalid witness script"
  ],
  [
    "0x09 0x300602010102010101",
    "0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 CHECKSIG NOT",
    "DERSIG,NULLFAIL",
    "NULLFAIL",
    "BIP66 example 4, with DERSIG and NULLFAIL, non-null DER-compliant signature"
  ],
  [
    "0 0x47 0x304402200abeb4bd07f84222f474aed558cfbdfc0b4e96cde3c2935ba7098b1ff0bd74c302204a04c1ca67b2a20abee210cf9a21023edccbbf8024b988812634233115c6b73901 0x47 0x304402200abeb4bd07f84222f474aed558cfbdfc0b4e96cde3c2935ba7098b1ff0bd74c302204a04c1ca67b2a20abee210cf9a21023edccbbf8024b988812634233115c6b73901",
    "2 0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 0x21 0x038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508 2 CHECKMULTISIG",
    "SIGPUSHONLY",
    "OK",
    "2-of-2 with two identical keys and sigs pushed"
  ],
  [
    "11 0x47 0x304402200a5c6163f07b8d3b013c4d1d6dba25e780b39658d79ba37af7057a3b7f15ffa102201fd9b4eaa9943f734928b99a83592c2e7bf342ea2680f6a2bb705167966b742001",
    "0x41 0x0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 CHECKSIG",
    "CLEANSTACK,P2SH",
    "CLEANSTACK",
    "P2PK with unnecessary input"
  ],
  [
    "0x47 0x304402202f7505132be14872581f35d74b759212d9da40482653f1ffa3116c3294a4a51702206adbf347a2240ca41c66522b1a22a41693610b76a8e7770645dc721d1635854f01 0x43 0x410479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8ac",
    "HASH160 0x14 0x31edc23bdafda4639e669f89ad6b2318dd79d032 EQUAL",
    "CLEANSTACK,P2SH",
    "OK",
    "P2SH with CLEANSTACK"
  ],
  [
    "",
    "0 0x20 0xb95237b48faaa69eb078e1170be3b5cbb3fddf16d0a991e14ad274f7b33a4f64",
    "P2SH,WITNESS",
    "WITNESS_PROGRAM_WITNESS_EMPTY",
    "P2WSH with empty witness"
  ],
  [
    "1",
    "IF 1 ENDIF",
    "P2SH,WITNESS,MINIMALIF",
    "OK"
  ],
  [
    [
      "1ffe1234567890",
      "00",
      "#SCRIPT# HASH256 DUP SHA1 DROP DUP DROP TOALTSTACK HASH256 DUP DROP TOALTSTACK FROMALTSTACK",
      "#CONTROLBLOCK#",
      1e-08
    ],
    "",
    "0x51 0x20 #TAPROOTOUTPUT#",
    "P2SH,WITNESS,TAPROOT",
    "OK",
    "TAPSCRIPT Tests testing tapscript with many different op codes including ALTSTACK interactions"
  ],
  [
    [
      "abcdef",
      "#SCRIPT# 1 IF SHA256 ENDIF SIZE SWAP DROP 32 EQUAL",
      "#CONTROLBLOCK#",
      1e-08
    ],
    "",
    "0x51 0x20 #TAPROOTOUTPUT#",
    "P2SH,WITNESS,TAPROOT",
    "OK",
    "TAPSCRIPT Test IF conditional when true"
  ],
  [
    [
      "abcdef",
      "#SCRIPT# 0 IF SHA256 ENDIF SIZE SWAP DROP 32 EQUAL",
      "#CONTROLBLOCK#",
      1e-08
    ],
    "",
    "0x51 0x20 #TAPROOTOUTPUT#",
    "P2SH,WITNESS,TAPROOT",
    "EVAL_FALSE",
    "TAPSCRIPT Test IF conditional when false"
  ],
  [
    [
      "aa",
      "bb",
      "cc",
      "#SCRIPT# EQUAL IF DROP DROP ENDIF",
      "#CONTROLBLOCK#",
      1e-08
    ],
    "",
    "0x51 0x20 #TAPROOTOUTPUT#",
    "P2SH,WITNESS,TAPROOT",
    "OK",
    "TAPSCRIPT Test that DROP operations do not execute inside of a false IF conditional"
  ],
  [
    [
      "aa",
      "#SCRIPT# 0 CHECKSIG",
      "#CONTROLBLOCK#",
      1e-08
    ],
    "",
    "0x51 0x20 #TAPROOTOUTPUT#",
    "P2SH,WITNESS,TAPROOT",
    "TAPSCRIPT_EMPTY_PUBKEY",
    "TAPSCRIPT: OP_CHECKSIG with empty pubkey must fail"
  ]
]
"####

example : completeBoundaryIndices.length = 18 := by native_decide

example : ((auditCoreScriptTests rejectingFixtureOracle completeBoundaryFixtures).toOption.map
    fun audit => audit.testRows == 18 && audit.matchedRows == 18 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

-- Expected tags participate only in comparison, even for cryptographic paths.
example : (checkCoreFixture rejectingFixtureOracle {
    witness := none, scriptSigSource := "0 0", scriptPubKeySource := "CHECKSIG",
    flagSource := "", expectedError := "UNKNOWN_EXPECTED_TAG", comments := [] }).toOption =
    some false := by native_decide

end LeanMiniscript.Extraction
