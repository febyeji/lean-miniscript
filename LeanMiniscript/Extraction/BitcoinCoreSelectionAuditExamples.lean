import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-! Selection-opcode fixture regressions from `src/test/data/script_tests.json`
at `bitcoinCoreScriptTestsCommit`. The source SHA-256 is
`bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5`.
Every unique row containing MIN, MAX, PICK or ROLL in either script is included,
with its zero-based upstream index. -/

private def selectionFixtureJson : String := r#"
[
  ["22 21 20", "0 PICK 20 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "1 PICK 21 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "2 PICK 22 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "0 ROLL 20 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "1 ROLL 21 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "2 ROLL 22 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "OK"],
  ["1 0 MIN", "0 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["0 1 MIN", "0 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["-1 0 MIN", "-1 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["0 -2147483647 MIN", "-2147483647 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["2147483647 0 MAX", "2147483647 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["0 100 MAX", "100 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["-100 0 MAX", "0 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["0 -2147483647 MAX", "0 NUMEQUAL", "P2SH,STRICTENC", "OK"],
  ["1 0 0 0 3", "PICK", "P2SH,STRICTENC", "OK"],
  ["1 0", "PICK", "P2SH,STRICTENC", "OK"],
  ["1 0 0 0 3", "ROLL", "P2SH,STRICTENC", "OK"],
  ["1 0", "ROLL", "P2SH,STRICTENC", "OK"],
  ["-1 0", "MIN", "P2SH,STRICTENC", "OK"],
  ["1 0", "MAX", "P2SH,STRICTENC", "OK"],
  ["1 0x02 0x0000", "PICK DROP", "", "OK"],
  ["1 0x02 0x0000", "ROLL DROP 1", "", "OK"],
  ["0 0x02 0x0000", "MIN DROP 1", "", "OK"],
  ["0x02 0x0000 0", "MIN DROP 1", "", "OK"],
  ["0 0x02 0x0000", "MAX DROP 1", "", "OK"],
  ["0x02 0x0000 0", "MAX DROP 1", "", "OK"],
  ["19 20 21", "PICK 19 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "0 PICK", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "-1 PICK", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["19 20 21", "0 PICK 20 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["19 20 21", "1 PICK 21 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["19 20 21", "2 PICK 22 EQUALVERIFY DEPTH 3 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["NOP", "0 ROLL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "-1 ROLL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["19 20 21", "0 ROLL 20 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["19 20 21", "1 ROLL 21 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["19 20 21", "2 ROLL 22 EQUALVERIFY DEPTH 2 EQUAL", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["1 1 1 3", "PICK", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0", "PICK 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1 1 1 3", "ROLL", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0", "ROLL 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "MIN", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "MAX", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1 0x02 0x0000", "PICK DROP", "MINIMALDATA", "SCRIPTNUM"],
  ["1 0x02 0x0000", "ROLL DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "MIN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "MIN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000", "MAX DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0x02 0x0000 0", "MAX DROP 1", "MINIMALDATA", "SCRIPTNUM"]
]
"#

private def selectionFixtureSourceIndices : List Nat :=
  [71, 72, 73, 74, 75, 76, 188, 189, 190, 191, 192, 193, 194, 195, 359, 360, 361, 362, 388, 389, 536, 537, 566, 567, 568, 569, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 868, 869, 870, 871, 895, 896, 959, 960, 989, 990, 991, 992]

example : selectionFixtureSourceIndices.length = 49 := by
  native_decide

example : selectionFixtureSourceIndices.eraseDups.length = 49 := by
  native_decide

-- Selected rows compare against their exact upstream expected result tags.
example : ((auditCoreScriptTests rejectingFixtureOracle selectionFixtureJson).toOption.map
    fun audit => audit.testRows == 49 && audit.comparedRows == 49 &&
      audit.matchedRows == 49 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

private def selectionSourceFixtures : List (String × String × Opcode) :=
  [("PICK", "0x79", .OP_PICK), ("ROLL", "0x7a", .OP_ROLL),
   ("MIN", "0xa3", .OP_MIN), ("MAX", "0xa4", .OP_MAX)]

example : selectionSourceFixtures.all (fun (name, raw, opcode) =>
    [name, raw].all fun source =>
      match parseCoreScriptSource source with
      | .ok [.op actual] => actual == opcode
      | _ => false) = true := by
  native_decide

private def selectionBoundaryFixtureJson : String := r#"
[
  ["1 -2", "0xa3 -2 EQUAL", "MINIMALDATA", "OK"],
  ["1 -2 MIN", "-2 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF MIN ENDIF 1", "MINIMALDATA", "OK"],
  ["1 -2", "0xa4 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 -2 MAX", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF MAX ENDIF 1", "MINIMALDATA", "OK"],
  ["19 20 1", "0x79 19 EQUALVERIFY 20 EQUALVERIFY 19 EQUAL", "MINIMALDATA", "OK"],
  ["19 20 1 PICK", "19 EQUALVERIFY 20 EQUALVERIFY 19 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF PICK ENDIF 1", "MINIMALDATA", "OK"],
  ["19 20 1", "0x7a 19 EQUALVERIFY 20 EQUAL", "MINIMALDATA", "OK"],
  ["19 20 1 ROLL", "19 EQUALVERIFY 20 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF ROLL ENDIF 1", "MINIMALDATA", "OK"],
  ["0x02 0x0100 0x02 0x0100", "MIN 1 EQUAL", "", "OK"],
  ["0x02 0x0180 0x02 0x0180", "MAX -1 EQUAL", "", "OK"],
  ["0x01 0x80 0", "MIN 0 EQUAL", "", "OK"],
  ["0 0x01 0x80", "MAX 0 EQUAL", "", "OK"],
  ["0x05 0xdeadbeef00 0", "PICK EQUAL", "MINIMALDATA", "OK"],
  ["0x05 0xdeadbeef00 0", "ROLL 0x05 0xdeadbeef00 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x04 0x00000000", "PICK EQUAL", "", "OK"],
  ["1 0x04 0x00000080", "ROLL", "", "OK"],
  ["1 2147483647", "PICK", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 -2147483647", "ROLL", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 2147483648", "PICK", "MINIMALDATA", "SCRIPTNUM"],
  ["1 -2147483648", "ROLL", "MINIMALDATA", "SCRIPTNUM"],
  ["2147483648", "PICK", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["2147483648", "ROLL", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["2147483648", "MIN", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["2147483648", "MAX", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

-- Local fixtures exercise raw bytes, scriptSig execution, canonical numeric outputs,
-- untouched selected bytes, inactive branches and numeric-error ordering.
example : ((auditCoreScriptTests rejectingFixtureOracle selectionBoundaryFixtureJson).toOption.map
    fun audit => audit.testRows == 28 && audit.comparedRows == 28 &&
      audit.matchedRows == 28 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

end LeanMiniscript.Extraction
