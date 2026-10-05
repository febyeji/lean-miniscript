import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-! Original MINIMALDATA push fixtures from the pinned Bitcoin Core revision.
Source SHA-256: `bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5`.
The first 20 rows exercise skipped nonminimal pushes, and the next 21 exercise
active nonminimal pushes. Source indices include documentation rows. -/

private def minimalDataSourceIndices : List Nat :=
  [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944]

private def minimalDataFixtureJson : String := r#"
[
  ["0 IF 0x4c 0x00 ENDIF 1", "", "MINIMALDATA", "OK", "non-minimal PUSHDATA1 ignored"],
  ["0 IF 0x4d 0x0000 ENDIF 1", "", "MINIMALDATA", "OK", "non-minimal PUSHDATA2 ignored"],
  ["0 IF 0x4c 0x00000000 ENDIF 1", "", "MINIMALDATA", "OK", "non-minimal PUSHDATA4 ignored"],
  ["0 IF 0x01 0x81 ENDIF 1", "", "MINIMALDATA", "OK", "1NEGATE equiv"],
  ["0 IF 0x01 0x01 ENDIF 1", "", "MINIMALDATA", "OK", "OP_1  equiv"],
  ["0 IF 0x01 0x02 ENDIF 1", "", "MINIMALDATA", "OK", "OP_2  equiv"],
  ["0 IF 0x01 0x03 ENDIF 1", "", "MINIMALDATA", "OK", "OP_3  equiv"],
  ["0 IF 0x01 0x04 ENDIF 1", "", "MINIMALDATA", "OK", "OP_4  equiv"],
  ["0 IF 0x01 0x05 ENDIF 1", "", "MINIMALDATA", "OK", "OP_5  equiv"],
  ["0 IF 0x01 0x06 ENDIF 1", "", "MINIMALDATA", "OK", "OP_6  equiv"],
  ["0 IF 0x01 0x07 ENDIF 1", "", "MINIMALDATA", "OK", "OP_7  equiv"],
  ["0 IF 0x01 0x08 ENDIF 1", "", "MINIMALDATA", "OK", "OP_8  equiv"],
  ["0 IF 0x01 0x09 ENDIF 1", "", "MINIMALDATA", "OK", "OP_9  equiv"],
  ["0 IF 0x01 0x0a ENDIF 1", "", "MINIMALDATA", "OK", "OP_10 equiv"],
  ["0 IF 0x01 0x0b ENDIF 1", "", "MINIMALDATA", "OK", "OP_11 equiv"],
  ["0 IF 0x01 0x0c ENDIF 1", "", "MINIMALDATA", "OK", "OP_12 equiv"],
  ["0 IF 0x01 0x0d ENDIF 1", "", "MINIMALDATA", "OK", "OP_13 equiv"],
  ["0 IF 0x01 0x0e ENDIF 1", "", "MINIMALDATA", "OK", "OP_14 equiv"],
  ["0 IF 0x01 0x0f ENDIF 1", "", "MINIMALDATA", "OK", "OP_15 equiv"],
  ["0 IF 0x01 0x10 ENDIF 1", "", "MINIMALDATA", "OK", "OP_16 equiv"],
  ["0x4c 0x00", "DROP 1", "MINIMALDATA", "MINIMALDATA", "Empty vector minimally represented by OP_0"],
  ["0x01 0x81", "DROP 1", "MINIMALDATA", "MINIMALDATA", "-1 minimally represented by OP_1NEGATE"],
  ["0x01 0x01", "DROP 1", "MINIMALDATA", "MINIMALDATA", "1 to 16 minimally represented by OP_1 to OP_16"],
  ["0x01 0x02", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x03", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x04", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x05", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x06", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x07", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x08", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x09", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0a", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0b", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0c", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0d", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0e", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x0f", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x01 0x10", "DROP 1", "MINIMALDATA", "MINIMALDATA"],
  ["0x4c 0x48 0x111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", "DROP 1", "MINIMALDATA", "MINIMALDATA", "PUSHDATA1 of 72 bytes minimally represented by direct push"],
  ["0x4d 0xFF00 0x111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", "DROP 1", "MINIMALDATA", "MINIMALDATA", "PUSHDATA2 of 255 bytes minimally represented by PUSHDATA1"],
  ["0x4e 0x00010000 0x11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", "DROP 1", "MINIMALDATA", "MINIMALDATA", "PUSHDATA4 of 256 bytes minimally represented by PUSHDATA2"]
]
"#

private def minimalDataAudit : Option CoreFixtureAudit :=
  (auditCoreScriptTests rejectingFixtureOracle minimalDataFixtureJson).toOption

example : minimalDataSourceIndices.length = 41 := by native_decide
example : minimalDataAudit.map CoreFixtureAudit.testRows = some 41 := by native_decide
example : minimalDataAudit.map CoreFixtureAudit.matchedRows = some 41 := by native_decide
example : minimalDataAudit.map CoreFixtureAudit.unsupportedRows = some 0 := by native_decide
example : minimalDataAudit.map CoreFixtureAudit.allComparedRowsMatch = some true := by native_decide

private def fixture (sig script expected : String) (flags : String := "MINIMALDATA") :
    CoreScriptTest where
  witness := none
  scriptSigSource := sig
  scriptPubKeySource := script
  flagSource := flags
  expectedError := expected
  comments := []

/-- Local regressions combine minimality, branch execution and earlier errors. -/
private def localFixtures : List CoreScriptTest := [
  fixture "0x4c0101" "1 EQUAL" "OK" "",
  fixture "" "0x4d010001 DROP 1" "MINIMALDATA",
  fixture "" "0x4e0100000001 DROP 1" "MINIMALDATA",
  fixture "" "0x4c00 DROP 1" "MINIMALDATA",
  fixture "" "0x0181 DROP 1" "MINIMALDATA",
  fixture "" "0 IF 0x4e00000000 ENDIF 1" "OK",
  fixture "" "0 IF 1 IF 0x4c0101 ENDIF ENDIF 1" "OK",
  fixture "" "1 IF 0 IF 0x4c0101 ENDIF ENDIF 1" "OK",
  fixture "" "0 IF 1 ELSE 0x4c0101 ENDIF" "MINIMALDATA",
  fixture "" "1 IF 0x4c0101 ENDIF" "MINIMALDATA",
  fixture "" "0 IF 0x4c0101 ELSE 1 ENDIF" "OK",
  fixture "" "RETURN 0x4c0101" "OP_RETURN",
  fixture "" "0 VERIFY 0x4c0101" "VERIFY",
  fixture "" "0x4c0101 RETURN" "MINIMALDATA",
  fixture "" "CAT 0x4c0101" "DISABLED_OPCODE",
  fixture "" "0x4c0101 CAT" "MINIMALDATA",
  fixture "" "0 IF 0x4c0101 CAT ENDIF 1" "DISABLED_OPCODE",
  fixture "" "0x4c0101 0x4d00" "MINIMALDATA",
  fixture "" "0 IF 0x4c0101 ENDIF 0x4d00" "BAD_OPCODE",
  fixture "" "0 IF 0x4d00" "BAD_OPCODE",
  fixture "" "0x4c02ff" "BAD_OPCODE",
  fixture "0x4c0101" "RETURN" "MINIMALDATA",
  fixture "0 IF 0x4c0101 ENDIF 1" "1 EQUAL" "OK",
  fixture "0x51" "1 EQUAL" "OK",
  fixture "0x0100" "DROP 1" "OK",
  fixture "0x0180" "DROP 1" "OK",
  fixture "0x0100" "1ADD" "SCRIPTNUM",
  fixture "0x0180" "1ADD" "SCRIPTNUM"
]

example : localFixtures.length = 28 := by native_decide
example : localFixtures.all (fun test =>
    (checkCoreFixture rejectingFixtureOracle test).toOption == some true) = true := by
  native_decide

-- Oversized PUSHDATA4 is also nonminimal: PUSH_SIZE wins in either branch.
private def oversizedNonMinimalPush : String :=
  "0x4e09020000" ++ String.join (List.replicate 521 "11")

example : ([oversizedNonMinimalPush, "0 IF " ++ oversizedNonMinimalPush ++ " ENDIF 1"] :
    List String).all (fun source =>
      (checkCoreFixture rejectingFixtureOracle
        (fixture "" source "PUSH_SIZE")).toOption == some true) = true := by
  native_decide

-- MINIMALDATA is checked before the instruction grows a full stack.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" (String.join (List.replicate 1000 "1 ") ++ "0x4c0101")
      "MINIMALDATA")).toOption = some true := by
  native_decide

-- IF consumes its condition from a full stack; the inactive push leaves 999 items.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" (String.join (List.replicate 999 "1 ") ++
      "0 IF 0x4c0101 ENDIF") "OK")).toOption = some true := by
  native_decide

-- The raw path conservatively excludes decoded signature operations, even
-- when a local prefix would reject or an inactive branch would skip them.
example : (["0x4c0101 CHECKSIG", "0 IF 0x4c0101 CHECKSIG ENDIF 1"] : List String).all
    (fun source => match prepareCoreFixture (fixture "" source "MINIMALDATA") with
      | .error (.legacyScriptPubKey .signatureOpcode) => true
      | _ => false) = true := by
  native_decide

-- Pushed bytes are payloads; the decoder does not execute their opcode values.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" "0x4c017e DROP 1" "MINIMALDATA")).toOption = some true := by
  native_decide

end LeanMiniscript.Extraction
