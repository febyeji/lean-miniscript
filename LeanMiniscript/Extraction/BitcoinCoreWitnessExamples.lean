import LeanMiniscript.Extraction.BitcoinCoreWitness
import LeanMiniscript.Extraction.CoreFixtureTemplates
import LeanMiniscript.Script.Codec.Deserialization
import LeanMiniscript.Script.RuntimeLimitsProofs

namespace LeanMiniscript.Extraction.BitcoinCoreWitnessExamples

open LeanMiniscript.Script LeanMiniscript.Bitcoin

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := by
  intro a b
  cases a <;> cases b
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : BEq (Except ε α) :=
  ⟨fun a b => decide (a = b)⟩

private def bytes (size : Nat) : ByteArray := ⟨(List.replicate size 0).toArray⟩

private def hex (text : String) : ByteArray :=
  match resolveCoreFixtureTemplates (fun _ => .error "no script templates") [text] with
  | .ok resolved => resolved.witness.head!
  | .error _ => ByteArray.empty

/-- Unit tests execute real modeled opcodes. Transaction signature verification
is tested by the complete fixture audit rather than this local adapter. -/
private def execute (flags : ScriptFlags) : CoreScriptExecutor := fun request => do
  let script ← (deserializeScript request.scriptBytes).mapError (fun _ => .script .badOpcode)
  let ctx : TxContext := {
    version := 1, locktime := 0, sequence := 0xffffffff, sigHash := ByteArray.empty
    sigVersion := request.sigVersion }
  match evaluateWithRuntimeLimits (CryptoOracle.pureLeanHashes (fun _ _ _ => false))
      script request.stack [] flags ctx request.validationWeight with
  | .failure error => throw (.script error)
  | .success stack _ _ => return stack

private def flags (minimalIf : Bool := false) : CoreVerificationFlags where
  script := {
    minimalIf := minimalIf
    minimalData := false
    nullDummy := false
    nullFail := false
    strictEncoding := false }
  witness := true
  p2sh := true
  taproot := true

private def failExecution : CoreScriptExecutor := fun _ => .error (.script .opReturn)

example :
    (decodeCoreWitnessProgram? (hex "00021234")).map Prod.fst = some 0 ∧
    (decodeCoreWitnessProgram? (hex "60021234")).map Prod.fst = some 16 ∧
    (decodeCoreWitnessProgram? (hex "4f021234")).isNone = true ∧
    (decodeCoreWitnessProgram? (hex "004c021234")).isNone = true ∧
    (decodeCoreWitnessProgram? (hex "000112")).isNone = true := by native_decide

private def p2wsh (script : ByteArray) (arguments : List ByteArray)
    (minimalIf : Bool := false) (wrapped : Bool := false) : Except CoreVerificationError Unit :=
  verifyCoreWitnessProgram (execute (flags minimalIf).script) (flags minimalIf)
    (arguments ++ [script]) 0 (LeanHash160.SHA256.hash script) wrapped

-- Pinned Core rows 1019/1020: execution failure and wrong script commitment.
example : p2wsh (hex "00") [] = .error (.script .evalFalse) := by native_decide
example : verifyCoreWitnessProgram failExecution flags [hex "51"] 0
    (hex "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d") false =
      .error .witnessProgramMismatch := by native_decide

-- Native and P2SH-wrapped witness-v0 share execution, including MINIMALIF.
-- Cases correspond to Core rows 1206–1230 and their wrapped copies 1232–1256.
example : [false, true].all (fun wrapped =>
    p2wsh (hex "635168") [hex "01"] false wrapped == .ok () &&
    p2wsh (hex "635168") [hex "02"] false wrapped == .ok () &&
    p2wsh (hex "635168") [hex "02"] true wrapped == .error (.script .minimalIf) &&
    p2wsh (hex "635168") [hex ""] true wrapped == .error (.script .cleanStack) &&
    p2wsh (hex "635168") [] false wrapped == .error (.script .stackUnderflow) &&
    p2wsh (hex "645168") [hex ""] false wrapped == .ok () &&
    p2wsh (hex "645168") [hex "01"] false wrapped == .error (.script .cleanStack) &&
    p2wsh (hex "645168") [hex "02"] true wrapped == .error (.script .minimalIf)) = true := by
  native_decide

example :
    verifyCoreWitnessProgram failExecution flags [] 0 (bytes 32) false =
      .error .witnessProgramWitnessEmpty ∧
    verifyCoreWitnessProgram failExecution flags [] 0 (bytes 20) false =
      .error .witnessProgramMismatch ∧
    verifyCoreWitnessProgram failExecution flags [bytes 521] 0 (bytes 31) false =
      .error .witnessProgramWrongLength := by native_decide

-- P2WPKH constructs the standard 25-byte script, preserving stack order.
private def inspectP2wpkh : CoreScriptExecutor := fun request =>
  if request.sigVersion = .witnessV0 && request.stack == [hex "bb", hex "aa"] &&
      request.scriptBytes.data == (hex "76a914000000000000000000000000000000000000000088ac").data then
    .ok [trueElement]
  else .error (.script .badOpcode)

example : verifyCoreWitnessProgram inspectP2wpkh flags [hex "aa", hex "bb"] 0
    (bytes 20) false = .ok () := by native_decide

example :
    p2wsh (hex "7551") [bytes 520] = .ok () ∧
    p2wsh (hex "7551") [bytes 521] = .error (.script .pushSize) ∧
    p2wsh (hex "") [] = .error (.script .cleanStack) := by native_decide

-- Native pay-to-anchor is exempt from the future-version policy; wrapped
-- programs and other future versions retain that policy check.
example :
    verifyCoreWitnessProgram failExecution flags [] 2 (bytes 32) false = .ok () ∧
    verifyCoreWitnessProgram failExecution { flags with discourageUpgradableWitnessProgram := true }
      [] 2 (bytes 32) false = .error .discourageUpgradableWitnessProgram ∧
    verifyCoreWitnessProgram failExecution { flags with discourageUpgradableWitnessProgram := true }
      [] 1 (hex "4e73") false = .ok () ∧
    verifyCoreWitnessProgram failExecution { flags with discourageUpgradableWitnessProgram := true }
      [] 1 (hex "4e73") true = .error .discourageUpgradableWitnessProgram := by native_decide

example :
    coreTapscriptHasOpSuccess (hex "504c") = .ok true ∧
    coreTapscriptHasOpSuccess (hex "4c0150") = .ok false ∧
    coreTapscriptHasOpSuccess (hex "4c0250") = .error (.script .badOpcode) ∧
    coreTapscriptHasOpSuccess (hex "4d010050") = .ok false ∧
    coreTapscriptHasOpSuccess (hex "4e0100000050") = .ok false := by native_decide

-- Empty scripts, zero-length pushes and long opcode sequences reach the end
-- without reporting OP_SUCCESS or exhausting the scanner's fuel.
example : ["", "00", "4c00", "4d0000", "4e00000000"].all (fun source =>
    coreTapscriptHasOpSuccess (hex source) == .ok false) = true ∧
    coreTapscriptHasOpSuccess ⟨(List.replicate 10000 0x61).toArray⟩ = .ok false := by
  native_decide

-- Every truncated length prefix and payload fails before a later success
-- byte. An earlier OP_SUCCESS still takes precedence over that malformed tail.
example : ["4c", "4d", "4d01", "4e", "4e01", "4e0100", "4e010000",
    "0250", "4c0250", "4d020050", "4e0200000050", "4e0000000150"].all (fun source =>
      coreTapscriptHasOpSuccess (hex source) == .error (.script .badOpcode) &&
      coreTapscriptHasOpSuccess (hex "50" ++ hex source) == .ok true) = true := by
  native_decide

-- Success bytes inside multi-byte-length pushes remain data; scanning resumes
-- at the first opcode after the full payload, including its high length bytes.
example : [(hex "4d0001", 256), (hex "4e00000100", 65536)].all (fun (header, size) =>
    let script := header ++ ⟨(List.replicate size 0x50).toArray⟩
    coreTapscriptHasOpSuccess script == .ok false &&
    coreTapscriptHasOpSuccess (script ++ hex "50") == .ok true &&
    coreTapscriptHasOpSuccess (script ++ hex "4c") == .error (.script .badOpcode)) = true := by
  native_decide

-- OP_SUCCESS precedes both initial stack limits and subsequent decoding.
example :
    executeCoreWitnessScript failExecution flags {
      scriptBytes := hex "504c", stack := List.replicate 1001 (bytes 521)
      sigVersion := .tapscript } = .ok () ∧
    executeCoreWitnessScript failExecution { flags with discourageOpSuccess := true } {
      scriptBytes := hex "504c", stack := [bytes 521], sigVersion := .tapscript } =
        .error .discourageOpSuccess ∧
    executeCoreWitnessScript failExecution flags {
      scriptBytes := hex "51", stack := List.replicate 1001 (bytes 521)
      sigVersion := .tapscript } = .error (.script .stackSize) := by native_decide

private def templateCompiler (source : String) : Except String ByteArray :=
  if source == " 0 CHECKSIG" then .ok (hex "00ac")
  else if source == " 1" then .ok (hex "51")
  else .error "unexpected test template source"

private def resolvedTrue :=
  resolveCoreFixtureTemplates templateCompiler ["aa", "#SCRIPT# 1", "#CONTROLBLOCK#"]

private def templateCommits : Bool :=
  match resolvedTrue with
  | .error _ => false
  | .ok templates =>
      match templates.outputKey, templates.witness.reverse with
      | some key, control :: script :: [argument] =>
          argument.data == (hex "aa").data &&
          (verifyTaprootControlBlock key script control).isOk &&
          !(verifyTaprootControlBlock key (hex "00") control).isOk &&
          match resolveCoreFixtureScriptPubKey templateCompiler templates
              "0x51 0x20 #TAPROOTOUTPUT#" with
          | .ok output => output.data == (⟨#[0x51, 0x20]⟩ ++ key).data
          | .error _ => false
      | _, _ => false

example : templateCommits = true := by native_decide

-- Core row 1262: the template's committed script reaches the actual Tapscript
-- empty-key rule, independently of the supplied ECDSA callback.
private def templateEmptyKey : Except String (Except CoreVerificationError Unit) := do
  let templates ← resolveCoreFixtureTemplates templateCompiler
    ["aa", "#SCRIPT# 0 CHECKSIG", "#CONTROLBLOCK#"]
  let key ← match templates.outputKey with
    | some key => pure key
    | none => throw "missing output"
  return verifyCoreWitnessProgram (execute flags.script) flags templates.witness 1 key false

example : templateEmptyKey = .ok (.error (.script .tapscriptEmptyPubkey)) := by native_decide

private def metadataPreserved : Bool :=
  match resolvedTrue with
  | .error _ => false
  | .ok templates =>
      match templates.outputKey with
      | none => false
      | some key =>
          let witness := templates.witness ++ [hex "5001"]
          let inspect : CoreScriptExecutor := fun request =>
            if request.sigVersion == .tapscript && request.stack == [hex "aa"] &&
                request.validationWeight == (serializeWitness witness).size + 50 &&
                request.annex == some (hex "5001") &&
                request.tapleafHash == some (tapleafHash (hex "51") 0xc0) then
              .ok [trueElement]
            else .error (.script .badOpcode)
          verifyCoreWitnessProgram inspect flags witness 1 key false == .ok ()

example : metadataPreserved = true := by native_decide

-- Key-path dispatch removes an annex only when a second witness item exists.
private def inspectKeyPath : CoreKeyPathChecker := fun signature output annex =>
  if signature.data == (hex "aa").data && output.size == 32 &&
      annex == some (hex "5001") then .ok ()
  else .error (.script .schnorrSig)

example :
    verifyCoreWitnessProgram failExecution flags [hex "aa", hex "5001"] 1
      (bytes 32) false inspectKeyPath = .ok () ∧
    verifyCoreWitnessProgram failExecution flags [hex "5001"] 1
      (bytes 32) false inspectKeyPath = .error (.script .schnorrSig) ∧
    verifyCoreWitnessProgram failExecution { flags with taproot := false } [] 1
      (bytes 32) false inspectKeyPath = .ok () ∧
    verifyCoreWitnessProgram failExecution flags [] 1 (bytes 32) false =
      .error .witnessProgramWitnessEmpty := by native_decide

-- Commitment errors occur before OP_SUCCESS and initial witness limits.
example :
    verifyCoreWitnessProgram failExecution flags
      [bytes 521, hex "50", bytes 32] 1 (bytes 32) false =
        .error .taprootWrongControlSize ∧
    verifyCoreWitnessProgram failExecution flags
      [bytes 521, hex "50", ⟨#[0xc0]⟩ ++ coreFixtureTemplateInternalKey] 1
      (bytes 32) false = .error .witnessProgramMismatch := by native_decide

example :
    (resolveCoreFixtureTemplates templateCompiler ["zz"]).isOk = false ∧
    (resolveCoreFixtureTemplates templateCompiler ["a"]).isOk = false ∧
    (resolveCoreFixtureTemplates templateCompiler ["#CONTROLBLOCK#"]).isOk = false ∧
    (resolveCoreFixtureScriptPubKey templateCompiler { witness := [] }
      "0x51 0x20 #TAPROOTOUTPUT#").isOk = false := by native_decide

end LeanMiniscript.Extraction.BitcoinCoreWitnessExamples
