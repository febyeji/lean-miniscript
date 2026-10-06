import LeanMiniscript.Script.State

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- VerifyScript boundary failures are separate from individual Script errors. -/
inductive CoreVerificationError where
  | script (error : ScriptError)
  | sigPushOnly
  | witnessProgramWrongLength
  | witnessProgramWitnessEmpty
  | witnessProgramMismatch
  | witnessMalleated
  | witnessMalleatedP2SH
  | witnessUnexpected
  | discourageUpgradableWitnessProgram
  | taprootWrongControlSize
  | discourageUpgradableTaprootVersion
  | discourageOpSuccess
  | opCodeSeparator
  | sigFindAndDelete
  /-- An execution boundary for which the caller has supplied no implementation. -/
  | unsupported (reason : String)
  deriving Repr, DecidableEq, BEq

/-- Core flags at the script-pair and witness-program boundary. -/
structure CoreVerificationFlags where
  script : ScriptFlags := {}
  p2sh : Bool := false
  sigPushOnly : Bool := false
  cleanStack : Bool := false
  witness : Bool := false
  taproot : Bool := false
  checkLockTimeVerify : Bool := false
  checkSequenceVerify : Bool := false
  discourageUpgradableWitnessProgram : Bool := false
  discourageUpgradableTaprootVersion : Bool := false
  discourageOpSuccess : Bool := false
  constScriptCode : Bool := false
  deriving Repr

/-- One raw Script evaluation. Stacks are top-first; wire-order witnesses are
reversed at their entry point. Transaction data and flags belong to the executor
closure; the request carries per-script signature hashing metadata. -/
structure CoreScriptExecutionRequest where
  scriptBytes : ByteArray
  stack : Stack := []
  sigVersion : SignatureVersion := .base
  validationWeight : Nat := 0
  annex : Option ByteArray := none
  tapleafHash : Option ByteArray := none
  leafVersion : UInt8 := 0xc0
  deriving Repr

abbrev CoreScriptExecutor :=
  CoreScriptExecutionRequest → Except CoreVerificationError Stack

/-- Transaction-backed Taproot key-path signature verification is injected at
the witness boundary independently of Script execution. -/
abbrev CoreKeyPathChecker :=
  ByteArray → ByteArray → Option ByteArray → Except CoreVerificationError Unit

/-- The script-pair boundary supplies the parsed program and whether it was
inside P2SH. Flags and transaction context are captured by this callback. -/
abbrev CoreWitnessVerifier :=
  List ByteArray → Nat → ByteArray → Bool → Except CoreVerificationError Unit

/-- Script-error rendering is supplied by the fixture boundary to keep this
module independent of source parsing and fixture preparation. -/
def CoreVerificationError.coreTag (error : CoreVerificationError)
    (scriptTag : ScriptError → String) : String :=
  match error with
  | .script error => scriptTag error
  | .sigPushOnly => "SIG_PUSHONLY"
  | .witnessProgramWrongLength => "WITNESS_PROGRAM_WRONG_LENGTH"
  | .witnessProgramWitnessEmpty => "WITNESS_PROGRAM_WITNESS_EMPTY"
  | .witnessProgramMismatch => "WITNESS_PROGRAM_MISMATCH"
  | .witnessMalleated => "WITNESS_MALLEATED"
  | .witnessMalleatedP2SH => "WITNESS_MALLEATED_P2SH"
  | .witnessUnexpected => "WITNESS_UNEXPECTED"
  | .discourageUpgradableWitnessProgram => "DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM"
  | .taprootWrongControlSize => "TAPROOT_WRONG_CONTROL_SIZE"
  | .discourageUpgradableTaprootVersion => "DISCOURAGE_UPGRADABLE_TAPROOT_VERSION"
  | .discourageOpSuccess => "DISCOURAGE_OP_SUCCESS"
  | .opCodeSeparator => "OP_CODESEPARATOR"
  | .sigFindAndDelete => "SIG_FINDANDDELETE"
  | .unsupported reason => "MODEL_UNSUPPORTED:" ++ reason

end LeanMiniscript.Extraction
