import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

/-! # Bitcoin Core fixture audit regressions -/

private def auditFixtureJson : String := r#"
[
  ["documentation"],
  ["1", "1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "VERIFY", "P2SH,STRICTENC", "VERIFY"],
  ["1", "1 EQUAL", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "PICK", "P2SH,STRICTENC", "OK"]
]
"#

private def auditFixture : Option CoreFixtureAudit :=
  (auditCoreScriptTests rejectingFixtureOracle auditFixtureJson).toOption

private def auditCountsMatch : Bool :=
  match auditFixture with
  | none => false
  | some audit =>
      audit.documentationRows == 1 && audit.testRows == 4 &&
        audit.matchedRows == 2 && audit.comparedRows == 3 &&
        audit.mismatches.length == 1 && audit.unsupportedRows == 1 &&
        !audit.allComparedRowsMatch

/-- The report separates exact matches, mismatches, and unsupported rows. -/
example : auditCountsMatch = true := by
  native_decide

/-- Mismatch details retain the upstream row index and both Core tags. -/
example : (auditFixture.bind fun audit => audit.mismatches.head?) =
    some {
      index := 3
      scriptSigSource := "1"
      scriptPubKeySource := "1 EQUAL"
      expectedTag := "EVAL_FALSE"
      actualTag := "OK"
    } := by
  native_decide

/-- Unsupported details preserve the structured importer reason. -/
example : (auditFixture.bind fun audit => audit.unsupported.head?) =
    some {
      index := 4
      scriptSigSource := "1"
      scriptPubKeySource := "PICK"
      reason := .scriptPubKey (.unsupportedToken "PICK")
    } := by
  native_decide

example : auditFixture.map CoreFixtureAudit.unsupportedReasonCounts =
    some [("script-pubkey-source", 1)] := by
  native_decide

example : auditFixture.map CoreFixtureAudit.unsupportedDetailCounts =
    some [("script-pubkey-source.unsupported-token.PICK", 1)] := by
  native_decide

private def sourceErrorDetailFixtures :
    List (CoreScriptSourceError × String) :=
  [(.unterminatedQuote, "unterminated-quote"),
   (.quoteInsideToken, "quote-inside-token"),
   (.invalidHex "0xz", "invalid-hex"),
   (.oddHexLength "0x0", "odd-hex-length"),
   (.unsupportedToken "PICK", "unsupported-token.PICK"),
   (.serialization (.pushDataTooLarge 4294967296),
      "serialization.push-data-too-large"),
   (.truncatedPushLength 0 2 1, "truncated-push-length"),
   (.truncatedPushData 0 2 1, "truncated-push-data"),
   (.unsupportedOpcode 3 0x61, "unsupported-opcode-byte.0x61"),
   (.decoderFuelExhausted 4, "decoder-fuel-exhausted")]

/-- A representative of every source-error constructor has a stable detail. -/
example : sourceErrorDetailFixtures.all fun (error, expected) =>
    error.detailCategory == expected := by
  native_decide

private def dropFixtureJson : String := r#"
[
  ["1 2", "DROP 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["", "DROP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "TOALTSTACK DROP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "DROP", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["", "0 IF DROP ENDIF 1", "P2SH,STRICTENC", "OK"],
  ["1 2 DROP", "1 EQUAL", "P2SH,STRICTENC", "OK"]
]
"#

/-- DROP covers stack order, empty main stacks, final acceptance, inactive
    branches, and scriptSig execution through the Core fixture importer. -/
example : ((auditCoreScriptTests rejectingFixtureOracle dropFixtureJson).toOption.map
    fun audit => audit.comparedRows == 6 && audit.matchedRows == 6 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def depthFixtureJson : String := r#"
[
  ["", "DEPTH 0 EQUAL", "P2SH,STRICTENC", "OK", "Test the test: we should have an empty stack after scriptSig evaluation"],
  ["0 IFDUP", "DEPTH 1 EQUALVERIFY 0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["1 IFDUP", "DEPTH 2 EQUALVERIFY 1 EQUALVERIFY 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0x05 0x0100000000 IFDUP", "DEPTH 2 EQUALVERIFY 0x05 0x0100000000 EQUAL", "P2SH,STRICTENC", "OK", "IFDUP dups non ints"],
  ["0 DROP", "DEPTH 0 EQUAL", "P2SH,STRICTENC", "OK"]
]
"#

/-- Verbatim rows from bitcoinCoreScriptTestsCommit cover DEPTH on empty and
    populated stacks, with non-numeric elements and preceding stack operations. -/
example : ((auditCoreScriptTests rejectingFixtureOracle depthFixtureJson).toOption.map
    fun audit => audit.comparedRows == 5 && audit.matchedRows == 5 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def depthBoundaryFixtureJson : String := r#"
[
  ["", "DEPTH", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1 2", "DEPTH 2 EQUALVERIFY 2 EQUALVERIFY 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["1", "TOALTSTACK DEPTH 0 EQUALVERIFY FROMALTSTACK 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["", "0 IF DEPTH ENDIF DEPTH 0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["DEPTH", "0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["", "0x74 0 EQUAL", "P2SH,STRICTENC", "OK"]
]
"#

/-- Local Core-format regressions cover final truth, stack order, alt-stack
    exclusion, inactive execution, scriptSig and raw-byte parsing. -/
example : ((auditCoreScriptTests rejectingFixtureOracle depthBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 6 && audit.matchedRows == 6 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def notFixtureJson : String := r#"
[
  ["0 NOT", "NOP", "P2SH,STRICTENC", "OK"],
  ["1 NOT", "0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["11 NOT", "0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0x01 0x00", "NOT", "P2SH,STRICTENC", "OK", "non-minimal-0 NOT"],
  ["0x01 0x80", "NOT", "P2SH,STRICTENC", "OK", "negative-0 NOT"],
  ["0x01 0x81", "NOT", "P2SH,STRICTENC", "EVAL_FALSE", "negative 1 NOT"],
  ["0x02 0x0000", "NOT DROP 1", "", "OK"],
  ["'abcdef' NOT", "0 EQUAL", "P2SH,STRICTENC", "SCRIPTNUM", "NOT is an arithmetic operand"],
  ["NOP", "NOT 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0x01 0x00", "NOT DROP 1", "MINIMALDATA", "SCRIPTNUM", "numequals 0"],
  ["0x01 0x80", "NOT DROP 1", "MINIMALDATA", "SCRIPTNUM", "0x80 (negative zero) numequals 0"],
  ["0x02 0x0500", "NOT DROP 1", "MINIMALDATA", "SCRIPTNUM", "numequals 5"],
  ["0x02 0x0580", "NOT DROP 1", "MINIMALDATA", "SCRIPTNUM", "numequals -5"],
  ["0x04 0xffff7f80", "NOT DROP 1", "MINIMALDATA", "SCRIPTNUM", "Minimal encoding is 0xffffff"]
]
"#

/-- Verbatim rows from bitcoinCoreScriptTestsCommit cover NOT in both scripts,
    canonical and non-minimal numbers, negative zero, underflow and overflow. -/
example : ((auditCoreScriptTests rejectingFixtureOracle notFixtureJson).toOption.map
    fun audit => audit.comparedRows == 14 && audit.matchedRows == 14 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def notBoundaryFixtureJson : String := r#"
[
  ["0", "0x91 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["-2147483647", "NOT 0 EQUAL", "MINIMALDATA", "OK"],
  ["2147483647", "NOT 0 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648", "NOT", "", "SCRIPTNUM"],
  ["", "0 IF NOT ENDIF 1", "P2SH,STRICTENC", "OK"]
]
"#

/-- Local Core-format rows pin the raw opcode, four/five-byte boundary and
    inactive underflow without changing the importer's support boundary. -/
example : ((auditCoreScriptTests rejectingFixtureOracle notBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 5 && audit.matchedRows == 5 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def withinFixtureJson : String := r#"
[
  ["0 0 1", "WITHIN", "P2SH,STRICTENC", "OK"],
  ["1 0 1", "WITHIN NOT", "P2SH,STRICTENC", "OK"],
  ["0 -2147483647 2147483647", "WITHIN", "P2SH,STRICTENC", "OK"],
  ["-1 -100 100", "WITHIN", "P2SH,STRICTENC", "OK"],
  ["11 -100 100", "WITHIN", "P2SH,STRICTENC", "OK"],
  ["-2147483647 -100 100", "WITHIN NOT", "P2SH,STRICTENC", "OK"],
  ["2147483647 -100 100", "WITHIN NOT", "P2SH,STRICTENC", "OK"],
  ["-1 -1 0", "WITHIN", "P2SH,STRICTENC", "OK"],
  ["0x02 0x0000 0 0", "WITHIN DROP 1", "", "OK"],
  ["0 0x02 0x0000 0", "WITHIN DROP 1", "", "OK"],
  ["0 0 0x02 0x0000", "WITHIN DROP 1", "", "OK"],
  ["1 1", "WITHIN", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0x02 0x0000 0 0", "WITHIN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0x02 0x0000 0", "WITHIN DROP 1", "MINIMALDATA", "SCRIPTNUM"],
  ["0 0 0x02 0x0000", "WITHIN DROP 1", "MINIMALDATA", "SCRIPTNUM"]
]
"#

/-- All fifteen verbatim WITHIN rows from bitcoinCoreScriptTestsCommit cover
    operand order, interval boundaries, signed numbers, underflow and each
    non-minimal operand position with minimal encoding enabled and disabled. -/
example : ((auditCoreScriptTests rejectingFixtureOracle withinFixtureJson).toOption.map
    fun audit => audit.comparedRows == 15 && audit.matchedRows == 15 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def withinBoundaryFixtureJson : String := r#"
[
  ["0 0 1", "0xa5", "MINIMALDATA", "OK"],
  ["0 0 0", "WITHIN", "MINIMALDATA", "EVAL_FALSE"],
  ["1 2 0", "WITHIN", "MINIMALDATA", "EVAL_FALSE"],
  ["-2147483647 -2147483647 2147483647", "WITHIN", "MINIMALDATA", "OK"],
  ["2147483648 0 1", "WITHIN DROP 1", "", "SCRIPTNUM"],
  ["0 -2147483648 1", "WITHIN DROP 1", "", "SCRIPTNUM"],
  ["0 0 2147483648", "WITHIN DROP 1", "", "SCRIPTNUM"],
  ["0x01 0x80 0 1", "WITHIN", "", "OK"],
  ["0x01 0x80 0 1", "WITHIN", "MINIMALDATA", "SCRIPTNUM"],
  ["", "WITHIN 1", "", "INVALID_STACK_OPERATION"],
  ["1", "WITHIN 1", "", "INVALID_STACK_OPERATION"],
  ["", "0 IF WITHIN ENDIF 1", "MINIMALDATA", "OK"],
  ["0 0 1 WITHIN", "1 EQUAL", "MINIMALDATA", "OK"],
  ["9 0 0 1", "WITHIN VERIFY 9 EQUAL", "MINIMALDATA", "OK"]
]
"#

/-- Separate local Core-format rows exercise raw byte parsing, equal/reversed
    bounds, four/five-byte limits, negative zero, inactive code and scriptSig. -/
example : ((auditCoreScriptTests rejectingFixtureOracle withinBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 14 && audit.matchedRows == 14 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def nipFixtureJson : String := r#"
[
  ["0 1", "NIP", "P2SH,STRICTENC", "OK"],
  ["0 1", "NIP", "P2SH,STRICTENC", "OK"],
  ["NOP", "NIP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "1 NIP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "1 0 NIP", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "NIP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- All six verbatim NIP rows from bitcoinCoreScriptTestsCommit cover success,
    zero/one-input underflow and a false surviving top item. -/
example : ((auditCoreScriptTests rejectingFixtureOracle nipFixtureJson).toOption.map
    fun audit => audit.comparedRows == 6 && audit.matchedRows == 6 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def nipBoundaryFixtureJson : String := r#"
[
  ["0 1", "0x77", "MINIMALDATA", "OK"],
  ["1 0", "NIP", "MINIMALDATA", "EVAL_FALSE"],
  ["9 8 7", "NIP 7 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x01 0x80", "NIP 0x01 0x80 EQUAL", "", "OK"],
  ["1 0x02 0x0100", "NIP 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["1 2147483648", "NIP 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648 1", "NIP", "MINIMALDATA", "OK"],
  ["0 1 NIP", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF NIP ENDIF 1", "MINIMALDATA", "OK"],
  ["9 0 1", "NIP TOALTSTACK 9 EQUALVERIFY FROMALTSTACK", "MINIMALDATA", "OK"],
  ["", "NIP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "NIP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Separate local Core-format regressions cover raw byte parsing, unchanged
    non-minimal and five-byte numbers, lower/alt stacks, inactive code and suffixes. -/
example : ((auditCoreScriptTests rejectingFixtureOracle nipBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 12 && audit.matchedRows == 12 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def overFixtureJson : String := r#"
[
  ["1 0", "OVER DEPTH 3 EQUALVERIFY", "P2SH,STRICTENC", "OK"],
  ["1 0", "OVER", "P2SH,STRICTENC", "OK"],
  ["NOP", "OVER 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "OVER", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["0 1", "OVER DEPTH 3 EQUALVERIFY", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "OVER", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- All six verbatim OVER rows from bitcoinCoreScriptTestsCommit cover copied
    values, stack depth, zero/one-input underflow and final truth. -/
example : ((auditCoreScriptTests rejectingFixtureOracle overFixtureJson).toOption.map
    fun audit => audit.comparedRows == 6 && audit.matchedRows == 6 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def overBoundaryFixtureJson : String := r#"
[
  ["1 0", "0x78", "MINIMALDATA", "OK"],
  ["0 1", "OVER", "MINIMALDATA", "EVAL_FALSE"],
  ["9 8 7", "OVER 8 EQUALVERIFY 7 EQUALVERIFY 8 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["0x01 0x80 1", "OVER 0x01 0x80 EQUAL", "", "OK"],
  ["0x02 0x0100 1", "OVER 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648 1", "OVER 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["1 2147483648", "OVER 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 0 OVER", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF OVER ENDIF 1", "MINIMALDATA", "OK"],
  ["8 7", "OVER TOALTSTACK 7 EQUALVERIFY 8 EQUALVERIFY FROMALTSTACK 8 EQUAL", "MINIMALDATA", "OK"],
  ["", "OVER 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "OVER 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Separate local Core-format rows cover raw opcode parsing, original stack
    order, exact non-minimal/five-byte copies, alt stacks, inactive code and suffixes. -/
example : ((auditCoreScriptTests rejectingFixtureOracle overBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 12 && audit.matchedRows == 12 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def rotFixtureJson : String := r#"
[
  ["22 21 20", "ROT 22 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "ROT DROP 20 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "ROT DROP DROP 21 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "ROT ROT 21 EQUAL", "P2SH,STRICTENC", "OK"],
  ["22 21 20", "ROT ROT ROT 20 EQUAL", "P2SH,STRICTENC", "OK"],
  ["1 0 0", "ROT", "P2SH,STRICTENC", "OK"],
  ["NOP", "ROT 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "1 ROT 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "1 2 ROT 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["NOP", "0 1 2 ROT", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1 1", "ROT", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- Verbatim ROT rows from bitcoinCoreScriptTestsCommit cover operand order,
    repeated rotation, final truth and all three underflow lengths. -/
example : ((auditCoreScriptTests rejectingFixtureOracle rotFixtureJson).toOption.map
    fun audit => audit.comparedRows == 11 && audit.matchedRows == 11 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def rotBoundaryFixtureJson : String := r#"
[
  ["1 2 3", "0x7b 1 EQUAL", "MINIMALDATA", "OK"],
  ["9 8 7 6", "ROT 8 EQUALVERIFY 6 EQUALVERIFY 7 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["0x01 0x80 1 2", "ROT 0x01 0x80 EQUAL", "", "OK"],
  ["0x02 0x0100 1 2", "ROT 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648 1 2", "ROT 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["0 1 2", "ROT", "MINIMALDATA", "EVAL_FALSE"],
  ["1 2 3 ROT", "1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF ROT ENDIF 1", "MINIMALDATA", "OK"],
  ["1", "0 IF ROT ENDIF 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 2", "0 IF ROT ENDIF 2 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["9 8 7", "ROT TOALTSTACK 7 EQUALVERIFY 8 EQUALVERIFY FROMALTSTACK 9 EQUAL", "MINIMALDATA", "OK"],
  ["", "ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 2", "ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Local Core-format regressions cover raw bytes, scriptSig, preserved numeric
    encodings, lower/alternate stacks and inactive branches. -/
example : ((auditCoreScriptTests rejectingFixtureOracle rotBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 14 && audit.matchedRows == 14 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoDupFixtureJson : String := r#"
[
  ["13 14", "2DUP ROT EQUALVERIFY EQUAL", "P2SH,STRICTENC", "OK"],
  ["0 1", "2DUP", "P2SH,STRICTENC", "OK"],
  ["NOP", "2DUP 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "2DUP 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "2DUP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- Verbatim 2DUP rows from bitcoinCoreScriptTestsCommit cover copy order,
    ROT continuation, final truth and zero/one-item underflow. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoDupFixtureJson).toOption.map
    fun audit => audit.comparedRows == 5 && audit.matchedRows == 5 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoDupBoundaryFixtureJson : String := r#"
[
  ["1 2", "0x6e 2 EQUALVERIFY 1 EQUALVERIFY 2 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["9 8 7", "2DUP 7 EQUALVERIFY 8 EQUALVERIFY 7 EQUALVERIFY 8 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["0 1", "2DUP 1 EQUALVERIFY 0 EQUALVERIFY 1 EQUALVERIFY 0 EQUAL", "MINIMALDATA", "OK"],
  ["1 0", "2DUP", "", "EVAL_FALSE"],
  ["0x01 0x80 1", "2DUP DROP 0x01 0x80 EQUAL", "", "OK"],
  ["0x02 0x0100 1", "2DUP DROP 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648 1", "2DUP DROP 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["1 2DUP", "NOP", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 2 2DUP", "2 EQUALVERIFY 1 EQUALVERIFY 2 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 2DUP ENDIF 1", "MINIMALDATA", "OK"],
  ["1", "0 IF 2DUP ENDIF 1 EQUAL", "MINIMALDATA", "OK"],
  ["8 7", "2DUP TOALTSTACK TOALTSTACK 7 EQUALVERIFY 8 EQUALVERIFY FROMALTSTACK 8 EQUALVERIFY FROMALTSTACK 7 EQUAL", "MINIMALDATA", "OK"]
]
"#

/-- Local Core-format rows cover raw opcode parsing, copy order, preserved
    byte encodings, scriptSig, alternate stacks and inactive execution. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoDupBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 12 && audit.matchedRows == 12 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def tuckFixtureJson : String := r#"
[
  ["0 1", "TUCK DEPTH 3 EQUALVERIFY SWAP 2DROP", "P2SH,STRICTENC", "OK"],
  ["0 1", "TUCK", "P2SH,STRICTENC", "OK"],
  ["NOP", "TUCK 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "TUCK 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1 0", "TUCK DEPTH 3 EQUALVERIFY SWAP 2DROP", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "TUCK", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- All six verbatim TUCK rows compare, including the two ending in 2DROP. -/
example : ((auditCoreScriptTests rejectingFixtureOracle tuckFixtureJson).toOption.map
    fun audit => audit.comparedRows == 6 && audit.matchedRows == 6 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def tuckBoundaryFixtureJson : String := r#"
[
  ["0 1", "0x7d DEPTH 3 EQUALVERIFY 1 EQUALVERIFY 0 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["1 0", "TUCK", "MINIMALDATA", "EVAL_FALSE"],
  ["9 8 7", "TUCK 7 EQUALVERIFY 8 EQUALVERIFY 7 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x01 0x80", "TUCK DROP DROP 0x01 0x80 EQUAL", "", "OK"],
  ["1 0x01 0x80", "TUCK DROP DROP 0x01 0x80 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x02 0x0100", "TUCK DROP DROP 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["1 2147483648", "TUCK DROP DROP 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["2147483648 1", "TUCK DROP 2147483648 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["0 1 TUCK", "1 EQUALVERIFY 0 EQUALVERIFY 1 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF TUCK ENDIF 1", "MINIMALDATA", "OK"],
  ["9 8 7", "TUCK TOALTSTACK 8 EQUALVERIFY 7 EQUALVERIFY 9 EQUALVERIFY FROMALTSTACK 7 EQUAL", "MINIMALDATA", "OK"],
  ["", "TUCK 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "TUCK 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Local Core-format rows check raw bytes, insertion order, exact numeric
    bytes, alternate stacks, inactive code and underflow before suffixes. -/
example : ((auditCoreScriptTests rejectingFixtureOracle tuckBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 13 && audit.matchedRows == 13 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoDropFixtureJson : String := r#"
[
  ["0 1", "TUCK DEPTH 3 EQUALVERIFY SWAP 2DROP", "P2SH,STRICTENC", "OK"],
  ["0 0", "2DROP 1", "P2SH,STRICTENC", "OK"],
  ["1 0", "TUCK DEPTH 3 EQUALVERIFY SWAP 2DROP", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "2DROP 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- Verbatim 2DROP blockers from bitcoinCoreScriptTestsCommit cover success,
    final false results, insufficient input, and TUCK continuations. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoDropFixtureJson).toOption.map
    fun audit => audit.comparedRows == 4 && audit.matchedRows == 4 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoDropBoundaryFixtureJson : String := r#"
[
  ["1 2", "0x6d 1", "MINIMALDATA", "OK"],
  ["9 8 7 6", "2DROP 8 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["1 2", "2DROP", "MINIMALDATA", "EVAL_FALSE"],
  ["1 2 3 2DROP", "1 EQUAL", "MINIMALDATA", "OK"],
  ["0x01 0x80 0x02 0x0100", "2DROP 1", "", "OK"],
  ["0x01 0x80 0x02 0x0100", "2DROP 1", "MINIMALDATA", "OK"],
  ["2147483647 -2147483647", "2DROP 1", "MINIMALDATA", "OK"],
  ["2147483648 -2147483648", "2DROP 1", "MINIMALDATA", "OK"],
  ["0x02 0x0100 1 2", "2DROP 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["9 8 7 6", "TOALTSTACK 2DROP FROMALTSTACK 6 EQUALVERIFY 9 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 2DROP ENDIF 1", "MINIMALDATA", "OK"],
  ["1", "0 IF 2DROP ENDIF", "MINIMALDATA", "OK"],
  ["", "2DROP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "2DROP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Separate local Core-format rows check raw bytes, remaining stack order,
    numeric bytes without decoding, alt stacks, inactive code and suffixes. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoDropBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 14 && audit.matchedRows == 14 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoRotFixtureJson : String := r#"
[
  ["25 24 23 22 21 20", "2ROT 24 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT DROP 25 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2DROP 20 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2DROP DROP 21 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2DROP 2DROP 22 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2DROP 2DROP DROP 23 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2ROT 22 EQUAL", "P2SH,STRICTENC", "OK"],
  ["25 24 23 22 21 20", "2ROT 2ROT 2ROT 20 EQUAL", "P2SH,STRICTENC", "OK"],
  ["1 2 3 4 5 6", "2ROT DEPTH 6 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0 1 0 0 0 0", "2ROT", "P2SH,STRICTENC", "OK"],
  ["1 1 1 1 1", "2ROT", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- All eleven verbatim 2ROT rows from bitcoinCoreScriptTestsCommit cover
    pair order, repeated rotation, stack depth, final truth and underflow. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoRotFixtureJson).toOption.map
    fun audit => audit.comparedRows == 11 && audit.matchedRows == 11 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoRotBoundaryFixtureJson : String := r#"
[
  ["1 2 3 4 5 6", "0x71 2 EQUALVERIFY 1 EQUALVERIFY 6 EQUALVERIFY 5 EQUALVERIFY 4 EQUALVERIFY 3 EQUAL", "MINIMALDATA", "OK"],
  ["9 1 2 3 4 5 6", "2ROT 2DROP 2DROP 2DROP 9 EQUAL", "MINIMALDATA", "OK"],
  ["1 0 3 4 5 6", "2ROT", "MINIMALDATA", "EVAL_FALSE"],
  ["1 2 3 4 5 6 2ROT", "2 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x01 0x80 3 4 5 6", "2ROT 0x01 0x80 EQUAL", "", "OK"],
  ["1 0x01 0x80 3 4 5 6", "2ROT 0x01 0x80 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x02 0x0100 3 4 5 6", "2ROT 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["1 2147483648 3 4 5 6", "2ROT 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["-2147483648 2 3 4 5 6", "2ROT DROP -2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 3 4 5 6", "2ROT TOALTSTACK 1 EQUALVERIFY FROMALTSTACK 2 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 2ROT ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2 3 4 5", "0 IF 2ROT ENDIF 5 EQUAL", "MINIMALDATA", "OK"],
  ["", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1 1", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1 1 1", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1 1 1 1", "2ROT 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Separate local Core-format rows check raw bytes, lower-stack order,
    numeric bytes without decoding, alt stacks, inactive code and every short input. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoRotBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 18 && audit.matchedRows == 18 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoSwapFixtureJson : String := r#"
[
  ["1 3 5 7", "2SWAP ADD 4 EQUALVERIFY ADD 12 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0 1 0 0", "2SWAP", "P2SH,STRICTENC", "OK"],
  ["NOP", "2SWAP 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "2 3 2SWAP 1", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1 1 1", "2SWAP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"]
]
"#

/-- All five verbatim 2SWAP rows from bitcoinCoreScriptTestsCommit cover
    pair order, final truth and stack underflow. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoSwapFixtureJson).toOption.map
    fun audit => audit.comparedRows == 5 && audit.matchedRows == 5 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def twoSwapBoundaryFixtureJson : String := r#"
[
  ["1 2 3 4", "0x72 2 EQUALVERIFY 1 EQUALVERIFY 4 EQUALVERIFY 3 EQUAL", "MINIMALDATA", "OK"],
  ["9 1 2 3 4", "2SWAP 2DROP 2DROP 9 EQUAL", "MINIMALDATA", "OK"],
  ["1 0 3 4", "2SWAP", "MINIMALDATA", "EVAL_FALSE"],
  ["1 2 3 4 2SWAP", "2 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x01 0x80 3 4", "2SWAP 0x01 0x80 EQUAL", "", "OK"],
  ["1 0x01 0x80 3 4", "2SWAP 0x01 0x80 EQUAL", "MINIMALDATA", "OK"],
  ["1 0x02 0x0100 3 4", "2SWAP 0x02 0x0100 EQUAL", "MINIMALDATA", "OK"],
  ["1 2147483648 3 4", "2SWAP 2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["-2147483648 2 3 4", "2SWAP DROP -2147483648 EQUAL", "MINIMALDATA", "OK"],
  ["1 2 3 4", "2SWAP TOALTSTACK 1 EQUALVERIFY FROMALTSTACK 2 EQUAL", "MINIMALDATA", "OK"],
  ["", "0 IF 2SWAP ENDIF 1", "MINIMALDATA", "OK"],
  ["1 2 3", "0 IF 2SWAP ENDIF 3 EQUAL", "MINIMALDATA", "OK"],
  ["", "2SWAP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1", "2SWAP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1", "2SWAP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"],
  ["1 1 1", "2SWAP 1", "MINIMALDATA", "INVALID_STACK_OPERATION"]
]
"#

/-- Separate local Core-format rows check raw bytes, lower-stack order,
    numeric bytes without decoding, alt stacks, inactive code and every short input. -/
example : ((auditCoreScriptTests rejectingFixtureOracle twoSwapBoundaryFixtureJson).toOption.map
    fun audit => audit.comparedRows == 16 && audit.matchedRows == 16 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

end LeanMiniscript.Extraction
