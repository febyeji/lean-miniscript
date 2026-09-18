import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Bitcoin.TaprootControlBlock
import LeanMiniscript.Miniscript.Acceptance

namespace LeanMiniscript.Extraction
open LeanMiniscript.Script LeanMiniscript.Bitcoin

/-- Errors at the native P2TR/script-path extraction boundary. Unsupported
key paths and future leaf versions describe model scope, not consensus failure. -/
inductive TaprootScriptPathError where
  | context (error : SighashError)
  | notNativeP2TR
  | nonemptyScriptSig
  | emptyWitness
  | keyPathUnsupported
  | leafVersionUnsupported (version : UInt8)
  | control (error : TaprootControlError)
  deriving Repr, DecidableEq, BEq

/-- Split wire-order script-path witness material, removing a last-element
annex only when at least two elements exist, as required by BIP341. -/
def parseTapscriptWitness (fullWitness : List ByteArray) :
    Except TaprootScriptPathError TapscriptWitness :=
  match fullWitness.reverse with
  | [] => .error .emptyWitness
  | last :: rest =>
      let hasAnnex := !rest.isEmpty && last.size > 0 && last[0]! == 0x50
      let elements := if hasAnnex then rest else last :: rest
      match elements with
      | [] => .error .emptyWitness
      | [_] => .error .keyPathUnsupported
      | control :: script :: reversedArguments => .ok {
          arguments := reversedArguments.reverse
          scriptBytes := script
          controlBlock := control
          annex := if hasAnnex then some last else none }

/-- Material prepared for the modeled Tapscript entry point. Obtaining this
from the preparation function validates its native-output commitment. The
record itself is raw data, with no constructor-level proof invariant. -/
structure PreparedTapscript where
  witness : TapscriptWitness
  context : TxContext
  deriving Repr

/-- Validate transaction-context shape and a wire-order script-path witness's
commitment to the selected native P2TR spent output. Execution, flags and final
acceptance are separate; key paths/future leaf versions remain unsupported. -/
def prepareCommittedTapscriptTransaction
    (fullWitness : List ByteArray) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except TaprootScriptPathError PreparedTapscript := do
  let ctx ← (TxContext.fromTaproot {
    transaction := transaction, spentOutputs := spentOutputs, inputIndex := inputIndex }).mapError
      TaprootScriptPathError.context
  let spent := spentOutputs[inputIndex]!
  let program := spent.scriptPubKey
  if program.size ≠ 34 || program[0]! != 0x51 || program[1]! != 0x20 then
    throw .notNativeP2TR
  if (transaction.inputs[inputIndex]!).scriptSig.size ≠ 0 then throw .nonemptyScriptSig
  let witness ← parseTapscriptWitness fullWitness
  let commitment ← (verifyTaprootControlBlock (program.extract 2 34)
    witness.scriptBytes witness.controlBlock).mapError TaprootScriptPathError.control
  if commitment.leafVersion != 0xc0 then
    throw (.leafVersionUnsupported commitment.leafVersion)
  return { witness := witness, context := ctx }

/-- Execute a committed native P2TR script-path witness with transaction-backed
hashing and the full witness budget. Preparation checks the commitment against
the selected spent output before initial argument limits and execution. Final
acceptance is separate; execution enforces runtime stack/push limits. Transaction
validity and prevout provenance remain outside this model. The AST must serialize to the
committed script bytes. -/
def execCommittedTapscriptTransaction (oracle : CryptoOracle) (script : Script)
    (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except TaprootScriptPathError WeightedResult := do
  let prepared ← prepareCommittedTapscriptTransaction fullWitness transaction spentOutputs inputIndex
  return evaluateTapscript oracle script prepared.witness flags prepared.context

/-- Deterministic commitment/setup checks preserve the evaluator's existing
conditional oracle-refinement guarantee. This does not prove curve correctness. -/
theorem execCommittedTapscriptTransaction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    execCommittedTapscriptTransaction oracle script fullWitness flags transaction spentOutputs inputIndex =
      execCommittedTapscriptTransaction CryptoOracle.model script fullWitness flags transaction spentOutputs inputIndex := by
  simp only [execCommittedTapscriptTransaction, evaluateTapscript_eq_model agreement]

/-- Keep setup/commitment errors distinct from modeled execution and acceptance
    errors, including unsupported Miniscript flag settings. -/
inductive TaprootVerificationError where
  | setup (error : TaprootScriptPathError)
  | script (error : ScriptError)
  deriving Repr, DecidableEq, BEq

/-- Check a committed native P2TR script-path witness through final modeled
    Miniscript acceptance, returning its unused signature budget. Setup and
    commitment checks precede the flag contract, initial limits and execution.
    This is not full Bitcoin consensus verification: OP_SUCCESSx, key paths,
    future leaf versions and arbitrary raw-script parsing are outside the model. -/
def verifyCommittedTapscriptTransaction (oracle : CryptoOracle) (script : Script)
    (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except TaprootVerificationError Nat := do
  let prepared ← (prepareCommittedTapscriptTransaction fullWitness transaction spentOutputs inputIndex).mapError
    TaprootVerificationError.setup
  (Miniscript.checkTapscriptAcceptance oracle script prepared.witness flags prepared.context).mapError
    TaprootVerificationError.script

theorem verifyCommittedTapscriptTransaction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    verifyCommittedTapscriptTransaction oracle script fullWitness flags transaction spentOutputs inputIndex =
      verifyCommittedTapscriptTransaction CryptoOracle.model script fullWitness flags transaction spentOutputs inputIndex := by
  simp only [verifyCommittedTapscriptTransaction, Miniscript.checkTapscriptAcceptance,
    evaluateTapscript_eq_model agreement]

/-- After successful commitment preparation, the public verification entry
    accepts exactly the witnesses satisfying the modeled acceptance predicate.
    A raw PreparedTapscript value alone is not evidence of preparation. -/
theorem verifyCommittedTapscriptTransaction_iff
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat)
    {prepared : PreparedTapscript}
    (preparation : prepareCommittedTapscriptTransaction fullWitness transaction spentOutputs inputIndex =
      .ok prepared) :
    (∃ weight, verifyCommittedTapscriptTransaction oracle script fullWitness flags
      transaction spentOutputs inputIndex = .ok weight) ↔
      Miniscript.TapscriptAccepts script prepared.witness flags prepared.context := by
  rw [← Miniscript.checkTapscriptAcceptance_iff agreement]
  simp only [verifyCommittedTapscriptTransaction, preparation, Except.mapError, bind, Except.bind]
  cases Miniscript.checkTapscriptAcceptance oracle script prepared.witness flags prepared.context <;> simp

end LeanMiniscript.Extraction
