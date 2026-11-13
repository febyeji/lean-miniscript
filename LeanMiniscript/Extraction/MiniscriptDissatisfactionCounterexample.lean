import LeanMiniscript.Extraction.MiniscriptCompilation
import LeanMiniscript.Extraction.BitcoinCoreWitnessV0Proofs

/-!
A sane, dissatisfiable P2WSH fragment can exceed the operation limit when its
satisfaction path set is empty. `n:` repeated 202 times around `0` serializes
to 203 bytes and generates an empty dissatisfaction, but Core stops at OP_COUNT.

TODO(MF-732): reconcile the dissatisfaction obligation with the sanity boundary.
`incompatible` retains the obligation's abstract cryptographic/run and truthy
program premises; it does not assert that those premises hold unconditionally.
-/

namespace LeanMiniscript.Extraction.DissatisfactionCounterexample

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script
open LeanMiniscript.Bitcoin

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 2000000

def wrapN : Nat → CoreFragment → CoreFragment
  | 0, fragment => fragment
  | n + 1, fragment => .n (wrapN n fragment)
def fragment := wrapN 202 .zero

def flags : CoreVerificationFlags := { witness := true, script := {} }

def context : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty, sigVersion := .witnessV0 }

def bytes := ByteArray.mk (#[0] ++ Array.replicate 202 0x92)

theorem validDissatisfiable : ValidDissatisfiableMiniscript .p2wsh fragment := by
  refine ⟨{ z := true, d := true, u := true }, ⟨?_, ?_⟩, rfl⟩
  · decide
  · exact (inferTyped .p2wsh fragment).get (by decide) |>.property

theorem generated (environment : SatEnv) : dissatisfy fragment environment = some [] := by
  rfl

theorem serialized : serializeScript (compile fragment) = .ok bytes := by rfl

def sane : SaneFragment .p2wsh :=
  (checkSane .p2wsh fragment).toOption.get (by decide)

theorem resourceCounterexample :
    ValidDissatisfiableMiniscript .p2wsh sane.checked.fragment ∧
    (∀ environment, dissatisfy sane.checked.fragment environment = some []) ∧
    nonPushOpCount sane.compile > MAX_OPS_PER_SCRIPT := by
  refine ⟨validDissatisfiable, generated, ?_⟩
  decide


theorem rawOpCount :
    executeCoreScript flags context (fun _ _ => CryptoOracle.model)
      { scriptBytes := bytes, stack := [], sigVersion := .witnessV0 } =
      .error (.script .opCount) := by
  cbv

theorem coreOpCount
    (programTruth : castToBool (LeanHash160.SHA256.hash bytes) = true) :
    coreVerifyScript flags context (fun _ _ => CryptoOracle.model)
      (fun _ _ _ => .ok ()) ByteArray.empty (ScriptBytes.p2wsh bytes) [bytes] =
      .error (.script .opCount) := by
  have witnessFailure : verifyCoreWitnessProgram
      (executeCoreScript flags context (fun _ _ => CryptoOracle.model)) flags
      [bytes] 0 (LeanHash160.SHA256.hash bytes) false (fun _ _ _ => .ok ()) =
      .error (.script .opCount) := by
    simp [verifyCoreWitnessProgram, sha256_size, executeCoreWitnessScript,
      rawOpCount, bind, Except.bind]
  have empty : executeCoreScript flags context (fun _ _ => CryptoOracle.model)
      { scriptBytes := ByteArray.empty } = .ok [] := by
    simp [executeCoreScript, CoreScriptExecution.executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have pub := executeCoreScript_p2wshOutput flags context
    (fun _ _ => CryptoOracle.model) bytes
  simp only [coreVerifyScript, verifyScriptWith, verifyCoreScripts, pushOnly, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool (LeanHash160.SHA256.hash bytes) then .ok ()
      else .error (CoreVerificationError.script .evalFalse)) _) = _
  have enabled : flags.witness = true := rfl
  simp [programTruth, enabled, decodeCoreWitnessProgram_p2wsh,
    witnessFailure, ByteArray.size_empty, Except.bind]


theorem incompatible
    (environment : SatEnv)
    (hashes : ∀ data, (LeanMiniscript.Script.hash160 data).size = 20)
    (programTruth : castToBool (LeanHash160.SHA256.hash bytes) = true)
    (run : CompiledScriptRun .p2wsh environment flags context
      (fun _ _ => CryptoOracle.model) bytes) :
    ¬ P2WSHDissatisfaction := by
  intro claimed
  have predicted := claimed sane bytes (ScriptBytes.p2wsh bytes) [bytes]
    environment flags context (fun _ _ => CryptoOracle.model)
    (fun _ _ _ => .ok ()) [] ⟨serialized, hashes⟩ ⟨rfl, rfl, programTruth⟩
    run validDissatisfiable (generated environment)
  change coreVerifyScript flags context (fun _ _ => CryptoOracle.model)
    (fun _ _ _ => .ok ()) ByteArray.empty (ScriptBytes.p2wsh bytes) [bytes] =
      .error (.script .evalFalse) at predicted
  rw [coreOpCount programTruth] at predicted
  cases predicted

end LeanMiniscript.Extraction.DissatisfactionCounterexample
