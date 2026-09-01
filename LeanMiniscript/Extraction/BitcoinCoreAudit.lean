import LeanMiniscript.Extraction.BitcoinCoreFixtures

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-!
# Bitcoin Core fixture audit

This module turns a complete parsed `script_tests.json` document into a stable
report. Unsupported rows remain visible, while every row admitted by the
current model is compared against its exact Bitcoin Core result tag.
-/

/-- One supported row whose modeled result differs from the pinned Core tag. -/
structure CoreFixtureMismatch where
  index : Nat
  scriptSigSource : String
  scriptPubKeySource : String
  expectedTag : String
  actualTag : String
  deriving Repr, DecidableEq

/-- One row intentionally excluded from the current comparison boundary. -/
structure CoreFixtureUnsupportedRow where
  index : Nat
  scriptSigSource : String
  scriptPubKeySource : String
  reason : CoreFixtureUnsupported
  deriving Repr, DecidableEq

/-- Reproducible summary of one complete Core fixture document. -/
structure CoreFixtureAudit where
  documentationRows : Nat := 0
  testRows : Nat := 0
  matchedRows : Nat := 0
  mismatches : List CoreFixtureMismatch := []
  unsupported : List CoreFixtureUnsupportedRow := []
  deriving Repr, DecidableEq

/-- Stable category used to summarize an unsupported fixture reason. -/
def CoreFixtureUnsupported.category : CoreFixtureUnsupported → String
  | .witnessCase => "witness"
  | .scriptSig _ => "script-sig-source"
  | .scriptPubKey _ => "script-pubkey-source"
  | .unsupportedFlag _ => "flag"
  | .p2shEvaluation => "p2sh"
  | .signatureOpcode => "signature-result"
  | .nonMinimalPushEncoding => "non-minimal-push"
  | .inactiveTimelockOpcode _ => "inactive-timelock"
  | .expectedError _ => "expected-error"

namespace CoreFixtureAudit

/-- Number of rows actually compared with the evaluator. -/
def comparedRows (audit : CoreFixtureAudit) : Nat :=
  audit.matchedRows + audit.mismatches.length

/-- Number of rows outside the documented model boundary. -/
def unsupportedRows (audit : CoreFixtureAudit) : Nat :=
  audit.unsupported.length

/-- Whether every supported row produced its expected exact Core tag. -/
def allComparedRowsMatch (audit : CoreFixtureAudit) : Bool :=
  audit.mismatches.isEmpty

private def incrementCategory (wanted : String) :
    List (String × Nat) → List (String × Nat)
  | [] => [(wanted, 1)]
  | (category, count) :: rest =>
      if category == wanted then (category, count + 1) :: rest
      else (category, count) :: incrementCategory wanted rest

/-- Counts of unsupported rows grouped by stable model-boundary category. -/
def unsupportedReasonCounts (audit : CoreFixtureAudit) : List (String × Nat) :=
  audit.unsupported.foldl (fun counts row =>
    incrementCategory row.reason.category counts) []

end CoreFixtureAudit

/-- Executable hashes paired with signature callbacks that always reject.

    This is suitable for the current pinned supported subset: its admitted
    signature-opcode rows fail before callback results affect the outcome. -/
def rejectingFixtureOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => false)
    (fun _signatures _pubkeys _sigHash => false)

private def auditCoreFixtureEntry (oracle : CryptoOracle)
    (audit : CoreFixtureAudit) (indexed : CoreFixtureEntry × Nat) :
    CoreFixtureAudit :=
  let (entry, index) := indexed
  match entry with
  | .comment _ =>
      { audit with documentationRows := audit.documentationRows + 1 }
  | .test test =>
      let counted := { audit with testRows := audit.testRows + 1 }
      match prepareCoreFixture test with
      | .error reason =>
          { counted with
            unsupported := {
              index := index
              scriptSigSource := test.scriptSigSource
              scriptPubKeySource := test.scriptPubKeySource
              reason := reason
            } :: counted.unsupported }
      | .ok fixture =>
          let actualTag := (runCoreFixture oracle fixture).coreTag
          if actualTag == test.expectedError then
            { counted with matchedRows := counted.matchedRows + 1 }
          else
            { counted with
              mismatches := {
                index := index
                scriptSigSource := test.scriptSigSource
                scriptPubKeySource := test.scriptPubKeySource
                expectedTag := test.expectedError
                actualTag := actualTag
              } :: counted.mismatches }

/-- Audit parsed Core entries without dropping documentation or unsupported
    tests. Mismatch and unsupported details retain source-file order. -/
def auditCoreFixtureEntries (oracle : CryptoOracle)
    (entries : List CoreFixtureEntry) : CoreFixtureAudit :=
  let reversed := entries.zipIdx.foldl (auditCoreFixtureEntry oracle) {}
  { reversed with
    mismatches := reversed.mismatches.reverse
    unsupported := reversed.unsupported.reverse }

/-- Parse and audit a complete Bitcoin Core `script_tests.json` document. -/
def auditCoreScriptTests (oracle : CryptoOracle) (input : String) :
    Except CoreFixtureJsonError CoreFixtureAudit := do
  return auditCoreFixtureEntries oracle (← parseCoreScriptTests input)

end LeanMiniscript.Extraction
