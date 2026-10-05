import LeanMiniscript.Extraction.BitcoinCoreLegacyScript

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- Original script size is checked before any instruction or stack access. -/
theorem runCoreLegacyScript_scriptSize (oracle : CryptoOracle)
    (program : CoreLegacyProgram) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (large : program.byteSize > 10000) :
    runCoreLegacyScript oracle program stack flags ctx = .error .scriptSize := by
  simp only [runCoreLegacyScript, if_pos large]
  rfl

/-- Admission recognizes the same script-size failure without visiting signatures. -/
theorem checkCoreLegacyWithoutVerifier_scriptSize (oracle : CryptoOracle)
    (program : CoreLegacyProgram) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (large : program.byteSize > 10000) :
    checkCoreLegacyWithoutVerifier oracle program stack flags ctx =
      .ok (.error .scriptSize) := by
  simp [checkCoreLegacyWithoutVerifier, large]

/-- Oversized pushes precede opcode accounting in every execution branch. -/
theorem coreLegacyNextCount_pushSize (element : ScriptElement) (minimal : Bool)
    (state : RuntimeState) (flags : ScriptFlags) (count : Nat)
    (large : element.pushSize > maxScriptElementSize) :
    coreLegacyNextCount (.modeled element minimal) state flags count =
      .error .pushSize := by
  simp only [coreLegacyNextCount, if_pos large]
  rfl

/-- A truncated push fails before the operation counter is examined. -/
theorem coreLegacyNextCount_malformedPush (state : RuntimeState)
    (flags : ScriptFlags) (count : Nat) :
    coreLegacyNextCount (.failure .badOpcode false false) state flags count =
      .error .badOpcode := by
  rfl

/-- A reached counted legacy failure first consumes its operation budget. -/
theorem coreLegacyNextCount_failureOverflow (error : ScriptError) (activeOnly : Bool)
    (state : RuntimeState) (flags : ScriptFlags) (count : Nat)
    (overflow : count + 1 > 201) :
    coreLegacyNextCount (.failure error activeOnly true) state flags count =
      .error .opCount := by
  cases error <;> cases activeOnly <;>
    simp [coreLegacyNextCount, CoreLegacyInstruction.opcodeCount, overflow] <;> rfl

/-- NOP counts even in an inactive branch, independently of the runtime state. -/
theorem coreLegacyNextCount_nop (state : RuntimeState) (flags : ScriptFlags)
    (count : Nat) :
    coreLegacyNextCount (.modeled (.op .OP_NOP)) state flags count =
      if count + 1 > 201 then .error .opCount else .ok (count + 1) := by
  simp [coreLegacyNextCount, CoreLegacyInstruction.opcodeCount, opcodeByte,
    ScriptElement.pushSize, maxScriptElementSize]
  split <;> rfl

/-- Multisig charges its key count before the remaining operands are decoded. -/
theorem coreLegacyNextCount_multisigKeys (state : RuntimeState) (flags : ScriptFlags)
    (count : Nat) (keyBytes : StackElement) (rest : Stack) (keys : Int)
    (active : state.conditions.all id = true) (top : state.stack = keyBytes :: rest)
    (decoded : decodeScriptNum keyBytes flags.minimalData maxArithmeticScriptNumBytes = .ok keys)
    (range : ¬ (keys < 0 ∨ (maxPubKeysPerMultiSig : Int) < keys))
    (initial : ¬ (count + 1 > 201)) :
    coreLegacyNextCount (.modeled (.op .OP_CHECKMULTISIG)) state flags count =
      if count + 1 + keys.toNat > 201 then .error .opCount
      else .ok (count + 1 + keys.toNat) := by
  simp [coreLegacyNextCount, CoreLegacyInstruction.opcodeCount, opcodeByte,
    ScriptElement.pushSize, maxScriptElementSize, active, top, decoded, range, initial, bind, Except.bind, pure, Except.pure, throw]
  split <;> rfl

/-- A resource or malformed-push failure terminates before the instruction and suffix. -/
theorem evaluateCoreLegacyWithLimits_countFailure (oracle : CryptoOracle)
    (instruction : CoreLegacyInstruction) (rest : List CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) (count : Nat)
    (error : ScriptError) (failed : coreLegacyNextCount instruction state flags count = .error error) :
    evaluateCoreLegacyWithLimits oracle (instruction :: rest) state flags ctx count =
      .error error := by
  simp [evaluateCoreLegacyWithLimits, failed, bind, Except.bind]

/-- Preflight returns reached resource errors before it considers verifier dependence. -/
theorem evaluateCoreLegacyWithoutVerifier_countFailure (oracle : CryptoOracle)
    (instruction : CoreLegacyInstruction) (rest : List CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) (count : Nat)
    (error : ScriptError) (failed : coreLegacyNextCount instruction state flags count = .error error) :
    evaluateCoreLegacyWithoutVerifier oracle (instruction :: rest) state flags ctx count =
      .ok (.error error) := by
  simp [evaluateCoreLegacyWithoutVerifier, failed]

/-- With the same oracle, admitted preflight execution returns exactly the
limited evaluator's result. This includes all reached script failures. -/
theorem evaluateCoreLegacyWithoutVerifier_agrees (oracle : CryptoOracle)
    (instructions : List CoreLegacyInstruction) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (count : Nat)
    (result : Except ScriptError RuntimeState)
    (admitted : evaluateCoreLegacyWithoutVerifier oracle instructions state flags ctx count =
      .ok result) :
    evaluateCoreLegacyWithLimits oracle instructions state flags ctx count = result := by
  induction instructions generalizing state count with
  | nil => simpa [evaluateCoreLegacyWithoutVerifier, evaluateCoreLegacyWithLimits] using admitted
  | cons instruction rest ih =>
      simp only [evaluateCoreLegacyWithoutVerifier] at admitted
      cases counted : coreLegacyNextCount instruction state flags count with
      | error error =>
          simp only [counted, Except.ok.injEq] at admitted
          rw [← admitted]
          simp [evaluateCoreLegacyWithLimits, counted, bind, Except.bind]
      | ok nextCount =>
          simp only [counted] at admitted
          split at admitted
          · contradiction
          · cases stepped : coreLegacyStep oracle instruction state flags ctx with
            | error error =>
                simp only [stepped, Except.ok.injEq] at admitted
                rw [← admitted]
                simp [evaluateCoreLegacyWithLimits, counted, stepped, bind, Except.bind]
            | ok next =>
                simp only [stepped] at admitted
                simpa [evaluateCoreLegacyWithLimits, counted, stepped, bind, Except.bind, pure, Except.pure, throw] using
                  ih next nextCount admitted

/-- The agreement also holds across the complete original-byte script boundary. -/
theorem checkCoreLegacyWithoutVerifier_agrees (oracle : CryptoOracle)
    (program : CoreLegacyProgram) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (result : Except ScriptError Stack)
    (admitted : checkCoreLegacyWithoutVerifier oracle program stack flags ctx = .ok result) :
    runCoreLegacyScript oracle program stack flags ctx = result := by
  unfold checkCoreLegacyWithoutVerifier at admitted
  split at admitted
  · rename_i large
    have resultEq := Except.ok.inj admitted
    rw [← resultEq]
    exact runCoreLegacyScript_scriptSize oracle program stack flags ctx large
  · rename_i bounded
    have notLarge : ¬ program.byteSize > 10000 := by omega
    cases checked : evaluateCoreLegacyWithoutVerifier oracle program.instructions
        { stack := stack, altStack := [], conditions := [], weight := 0 } flags ctx 0 with
    | error error => simp [checked, Except.map] at admitted
    | ok checkedResult =>
        have agreement := evaluateCoreLegacyWithoutVerifier_agrees oracle _ _ flags ctx 0
          checkedResult checked
        simp only [checked, Except.map, Except.ok.injEq] at admitted
        rw [← admitted]
        cases checkedResult <;> simp [runCoreLegacyScript, notLarge, agreement, bind, Except.bind, pure, Except.pure]

end LeanMiniscript.Extraction
