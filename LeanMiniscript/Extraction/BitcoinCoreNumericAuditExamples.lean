import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-! Numeric-opcode fixture regressions from `src/test/data/script_tests.json`
at `bitcoinCoreScriptTestsCommit`. The source SHA-256 is
`bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5`.
Every unique row containing one of the ten new opcode tokens in either script
is included below, with its zero-based upstream index. -/

private def numericFixtureJson : String := r#"
[
  ["1 1ADD", "2 EQUAL", "P2SH,STRICTENC", "OK"],
  ["111 1SUB", "110 EQUAL", "P2SH,STRICTENC", "OK"],
  ["111 1 ADD 12 SUB", "100 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0 ABS", "0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["16 ABS", "16 EQUAL", "P2SH,STRICTENC", "OK"],
  ["-16 ABS", "-16 NEGATE EQUAL", "P2SH,STRICTENC", "OK"],
  ["11 10 1 ADD", "NUMNOTEQUAL NOT", "P2SH,STRICTENC", "OK"],
  ["111 10 1 ADD", "NUMNOTEQUAL", "P2SH,STRICTENC", "OK"],
  ["11 10", "LESSTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["4 4", "LESSTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["10 11", "LESSTHAN", "P2SH,STRICTENC", "OK"],
  ["-11 11", "LESSTHAN", "P2SH,STRICTENC", "OK"],
  ["-11 -10", "LESSTHAN", "P2SH,STRICTENC", "OK"],
  ["11 10", "GREATERTHAN", "P2SH,STRICTENC", "OK"],
  ["4 4", "GREATERTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["10 11", "GREATERTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["-11 11", "GREATERTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["-11 -10", "GREATERTHAN NOT", "P2SH,STRICTENC", "OK"],
  ["11 10", "LESSTHANOREQUAL NOT", "P2SH,STRICTENC", "OK"],
  ["4 4", "LESSTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["10 11", "LESSTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["-11 11", "LESSTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["-11 -10", "LESSTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["11 10", "GREATERTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["4 4", "GREATERTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["10 11", "GREATERTHANOREQUAL NOT", "P2SH,STRICTENC", "OK"],
  ["-11 11", "GREATERTHANOREQUAL NOT", "P2SH,STRICTENC", "OK"],
  ["-11 -10", "GREATERTHANOREQUAL NOT", "P2SH,STRICTENC", "OK"],
  ["2147483647 2147483647 SUB", "0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["2147483647 NEGATE DUP ADD", "-4294967294 EQUAL", "P2SH,STRICTENC", "OK"],
  ["2147483647", "1ADD 2147483648 EQUAL", "P2SH,STRICTENC", "OK", "We can do math on 4-byte integers, and compare 5-byte ones"],
  ["2147483647", "1ADD 1", "P2SH,STRICTENC", "OK"],
  ["-2147483647", "1ADD 1", "P2SH,STRICTENC", "OK"],
  ["0", "1ADD", "P2SH,STRICTENC", "OK"],
  ["2", "1SUB", "P2SH,STRICTENC", "OK"],
  ["-1", "NEGATE", "P2SH,STRICTENC", "OK"],
  ["-1", "ABS", "P2SH,STRICTENC", "OK"],
  ["1 0", "SUB", "P2SH,STRICTENC", "OK"],
  ["-1 0", "NUMNOTEQUAL", "P2SH,STRICTENC", "OK"],
  ["-1 0", "LESSTHAN", "P2SH,STRICTENC", "OK"],
  ["1 0", "GREATERTHAN", "P2SH,STRICTENC", "OK"],
  ["0 0", "LESSTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["0 0", "GREATERTHANOREQUAL", "P2SH,STRICTENC", "OK"],
  ["0x02 0x0000", "1ADD DROP 1", "", "OK"],
  ["0x02 0x0000", "1SUB DROP 1", "", "OK"],
  ["0x02 0x0000", "NEGATE DROP 1", "", "OK"],
  ["0x02 0x0000", "ABS DROP 1", "", "OK"],
  ["0 0x02 0x0000", "SUB DROP 1", "", "OK"],
  ["0x02 0x0000 0", "SUB DROP 1", "", "OK"],
  ["0 0x02 0x0000", "NUMNOTEQUAL DROP 1", "", "OK"],
  ["0x02 0x0000 0", "NUMNOTEQUAL DROP 1", "", "OK"],
  ["0 0x02 0x0000", "LESSTHAN DROP 1", "", "OK"],
  ["0x02 0x0000 0", "LESSTHAN DROP 1", "", "OK"],
  ["0 0x02 0x0000", "GREATERTHAN DROP 1", "", "OK"],
  ["0x02 0x0000 0", "GREATERTHAN DROP 1", "", "OK"],
  ["0 0x02 0x0000", "LESSTHANOREQUAL DROP 1", "", "OK"],
  ["0x02 0x0000 0", "LESSTHANOREQUAL DROP 1", "", "OK"],
  ["0 0x02 0x0000", "GREATERTHANOREQUAL DROP 1", "", "OK"],
  ["0x02 0x0000 0", "GREATERTHANOREQUAL DROP 1", "", "OK"],
  ["11 1 ADD 12 SUB", "11 EQUAL", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["2147483648", "1ADD 1", "P2SH,STRICTENC", "SCRIPTNUM", "We cannot do math on 5-byte integers"],
  ["2147483648", "NEGATE 1", "P2SH,STRICTENC", "SCRIPTNUM", "We cannot do math on 5-byte integers"],
  ["-2147483648", "1ADD 1", "P2SH,STRICTENC", "SCRIPTNUM", "Because we use a sign bit, -2147483648 is also 5 bytes"],
  ["2147483647", "1ADD 1SUB 1", "P2SH,STRICTENC", "SCRIPTNUM", "We cannot do math on 5-byte integers, even if the result is 4-bytes"],
  ["2147483648", "1SUB 1", "P2SH,STRICTENC", "SCRIPTNUM", "We cannot do math on 5-byte integers, even if the result is 4-bytes"],
  ["NOP", "1ADD 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "1SUB 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "NEGATE 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "ABS 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "SUB", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "NUMNOTEQUAL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "LESSTHAN", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "GREATERTHAN", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "LESSTHANOREQUAL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "GREATERTHANOREQUAL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0x02 0x0000", "1ADD DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000", "1SUB DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000", "NEGATE DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000", "ABS DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "SUB DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "SUB DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "NUMNOTEQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "NUMNOTEQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "LESSTHAN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "LESSTHAN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "GREATERTHAN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "GREATERTHAN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "LESSTHANOREQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "LESSTHANOREQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "GREATERTHANOREQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "GREATERTHANOREQUAL DROP 1", "MINIMALDATA", "SCRIPTNUM"]
]
"#

private def numericFixtureSourceIndices : List Nat :=
  [129, 130, 131, 132, 133, 134, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 203, 205, 329, 330, 331, 370, 371, 372, 373, 377, 383, 384, 385, 386, 387, 538, 539, 540, 541, 546, 547, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 725, 842, 843, 844, 845, 846, 878, 879, 880, 881, 885, 890, 891, 892, 893, 894, 961, 962, 963, 964, 969, 970, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988]

-- Indices retain the complete selected source inventory, including cross-opcode rows.
example : numericFixtureSourceIndices.length = 91 := by
  native_decide

example : numericFixtureSourceIndices.eraseDups.length = 91 := by
  native_decide

-- All selected rows compare with the exact upstream expected result tag.
example : ((auditCoreScriptTests rejectingFixtureOracle numericFixtureJson).toOption.map
    fun audit => audit.testRows == 91 && audit.comparedRows == 91 &&
      audit.matchedRows == 91 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

private def numericSourceFixtures : List (String × String × Opcode) :=
  [("1ADD", "0x8b", .OP_1ADD),
   ("1SUB", "0x8c", .OP_1SUB),
   ("NEGATE", "0x8f", .OP_NEGATE),
   ("ABS", "0x90", .OP_ABS),
   ("SUB", "0x94", .OP_SUB),
   ("NUMNOTEQUAL", "0x9e", .OP_NUMNOTEQUAL),
   ("LESSTHAN", "0x9f", .OP_LESSTHAN),
   ("GREATERTHAN", "0xa0", .OP_GREATERTHAN),
   ("LESSTHANOREQUAL", "0xa1", .OP_LESSTHANOREQUAL),
   ("GREATERTHANOREQUAL", "0xa2", .OP_GREATERTHANOREQUAL)]

-- Core assembly names and raw opcode bytes select the same modeled instruction.
example : numericSourceFixtures.all (fun (name, raw, opcode) =>
    [name, raw].all fun source =>
      match parseCoreScriptSource source with
      | .ok [.op actual] => actual == opcode
      | _ => false) = true := by
  native_decide

private def numericBoundaryFixtureJson : String := r#"
[
  ["1", "0x8b 2 EQUAL", "MINIMALDATA", "OK"],
  ["1 1ADD", "2 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 1ADD ENDIF 1", "MINIMALDATA", "OK"],
  ["1", "0x8c 0 EQUAL", "MINIMALDATA", "OK"],
  ["1 1SUB", "0 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 1SUB ENDIF 1", "MINIMALDATA", "OK"],
  ["1", "0x8f -1 EQUAL", "MINIMALDATA", "OK"],
  ["1 NEGATE", "-1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF NEGATE ENDIF 1", "MINIMALDATA", "OK"],
  ["-1", "0x90 1 EQUAL", "MINIMALDATA", "OK"],
  ["-1 ABS", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF ABS ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0x94 -1 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 SUB", "-1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF SUB ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0x9e 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 NUMNOTEQUAL", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF NUMNOTEQUAL ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0x9f 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 LESSTHAN", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF LESSTHAN ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0xa0 0 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 GREATERTHAN", "0 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF GREATERTHAN ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0xa1 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 LESSTHANOREQUAL", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF LESSTHANOREQUAL ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2", "0xa2 0 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 GREATERTHANOREQUAL", "0 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF GREATERTHANOREQUAL ENDIF 1", "MINIMALDATA", "OK"],
  ["2147483647", "1ADD 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["-2147483647", "1SUB -2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["2147483647 -2147483647", "SUB 4294967294 EQUAL", "MINIMALDATA", "OK"],
  ["-2147483647 2147483647", "SUB -4294967294 EQUAL", "MINIMALDATA", "OK"],
  ["-2147483647", "1SUB NEGATE", "MINIMALDATA", "SCRIPTNUM"],
  ["2147483647 -2147483647", "SUB ABS", "MINIMALDATA", "SCRIPTNUM"]
]
"#

-- Local rows exercise raw bytes, scriptSig execution, inactive branches and wide results.
example : ((auditCoreScriptTests rejectingFixtureOracle numericBoundaryFixtureJson).toOption.map
    fun audit => audit.testRows == 36 && audit.comparedRows == 36 &&
      audit.matchedRows == 36 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

end LeanMiniscript.Extraction
