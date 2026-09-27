import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

/-! # Bitcoin Core fixture audit regressions -/

private def auditFixtureJson : String := r#"
[
  ["documentation"],
  ["1", "1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "VERIFY", "P2SH,STRICTENC", "VERIFY"],
  ["1", "1 EQUAL", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "DEPTH", "P2SH,STRICTENC", "OK"]
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
      scriptPubKeySource := "DEPTH"
      reason := .scriptPubKey (.unsupportedToken "DEPTH")
    } := by
  native_decide

example : auditFixture.map CoreFixtureAudit.unsupportedReasonCounts =
    some [("script-pubkey-source", 1)] := by
  native_decide

example : auditFixture.map CoreFixtureAudit.unsupportedDetailCounts =
    some [("script-pubkey-source.unsupported-token.DEPTH", 1)] := by
  native_decide

private def sourceErrorDetailFixtures :
    List (CoreScriptSourceError × String) :=
  [(.unterminatedQuote, "unterminated-quote"),
   (.quoteInsideToken, "quote-inside-token"),
   (.invalidHex "0xz", "invalid-hex"),
   (.oddHexLength "0x0", "odd-hex-length"),
   (.unsupportedToken "DEPTH", "unsupported-token.DEPTH"),
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

end LeanMiniscript.Extraction
