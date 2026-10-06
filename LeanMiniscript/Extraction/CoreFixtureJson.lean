import Lean.Data.Json

/-!
Pinned Bitcoin Core fixture metadata and positional JSON decoding.
-/

namespace LeanMiniscript.Extraction

open Lean

/-- Bitcoin Core revision used by the checked Script fixture subset. -/
def bitcoinCoreScriptTestsCommit : String :=
  "9be056a8a72b624dae9623b2f7bded92c2a21c91"

/-- Path of the authoritative fixture file within the pinned Bitcoin Core tree. -/
def bitcoinCoreScriptTestsPath : String :=
  "src/test/data/script_tests.json"

/-- One executable entry decoded from Bitcoin Core's positional JSON format. -/
structure CoreScriptTest where
  witness : Option Json
  scriptSigSource : String
  scriptPubKeySource : String
  flagSource : String
  expectedError : String
  comments : List String

/-- `script_tests.json` also contains one-string documentation rows. -/
inductive CoreFixtureEntry where
  | comment (text : String)
  | test (test : CoreScriptTest)

/-- A malformed JSON document or positional fixture entry. -/
inductive CoreFixtureJsonError where
  | invalidJson (message : String)
  | rootNotArray
  | entryNotArray (index : Nat)
  | invalidEntry (index : Nat) (message : String)
  deriving Repr, DecidableEq

private def jsonStringAt (entryIndex : Nat) (values : Array Json)
    (fieldIndex : Nat) (fieldName : String) :
    Except CoreFixtureJsonError String := do
  let value ← match values[fieldIndex]? with
    | some value => pure value
    | none => throw (.invalidEntry entryIndex s!"missing {fieldName}")
  match value with
  | .str text => pure text
  | _ => throw (.invalidEntry entryIndex s!"{fieldName} must be a string")

private def jsonComments (entryIndex : Nat) (values : Array Json)
    (start : Nat) : Except CoreFixtureJsonError (List String) := do
  let trailing := values.toList.drop start
  trailing.mapM fun value =>
    match value with
    | .str text => pure text
    | _ => throw (.invalidEntry entryIndex "comments must be strings")

private def parseFixtureEntry (index : Nat) (json : Json) :
    Except CoreFixtureJsonError CoreFixtureEntry := do
  let values ← match json with
    | .arr values => pure values
    | _ => throw (.entryNotArray index)
  if values.size = 1 then
    return .comment (← jsonStringAt index values 0 "comment")
  let (witness, firstField) :=
    match values[0]? with
    | some witness@(.arr _) => (some witness, 1)
    | _ => (none, 0)
  if values.size < firstField + 4 then
    throw (.invalidEntry index "expected scriptSig, scriptPubKey, flags, and result")
  return .test {
    witness := witness
    scriptSigSource := ← jsonStringAt index values firstField "scriptSig"
    scriptPubKeySource := ← jsonStringAt index values (firstField + 1) "scriptPubKey"
    flagSource := ← jsonStringAt index values (firstField + 2) "flags"
    expectedError := ← jsonStringAt index values (firstField + 3) "expected result"
    comments := ← jsonComments index values (firstField + 4)
  }

/-- Parse the complete positional JSON array without dropping documentation,
    witness, comment, flag, or expected-error fields. -/
def parseCoreScriptTests (input : String) :
    Except CoreFixtureJsonError (List CoreFixtureEntry) := do
  let json ← (Json.parse input).mapError .invalidJson
  let entries ← match json with
    | .arr entries => pure entries
    | _ => throw .rootNotArray
  entries.toList.zipIdx.mapM fun (entry, index) =>
    parseFixtureEntry index entry

end LeanMiniscript.Extraction
