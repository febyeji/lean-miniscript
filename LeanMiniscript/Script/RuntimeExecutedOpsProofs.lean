import LeanMiniscript.Script.RuntimeCompletenessProofs

namespace LeanMiniscript.Script

open RuntimeProjection

/-!
# Executed-path operation accounting

`staticOperationCount` charges every source multisignature for
`maxPubKeysPerMultiSig` keys. Outside Tapscript the runtime charges one
operation per visited opcode plus the decoded key count of each *active*
multisignature, so a successful run of `script` needs only
`executedOpCount script` plus the keys charged on the executed path. This file
rebuilds the raise/restore/completeness chain on that accounting, so a caller
that knows the executed multisignature keys (rather than the static per-source
bound) can complete a runtime execution.
-/

/-- Operations one visited element charges outside Tapscript: one per opcode,
    `codeSeparator`, or `illegalOpcode`, and one per `badOpcode` above OP_16. -/
def ScriptElement.executedOpCharge : ScriptElement → Nat
  | .op _ => 1
  | .codeSeparator _ => 1
  | .illegalOpcode _ => 1
  | .badOpcode opcode => if opcode.byte.toNat ≤ 0x60 then 0 else 1
  | _ => 0

/-- Sum of per-element executed charges. Unlike `staticOperationCount`,
    multisignatures contribute only the opcode itself. -/
def executedOpCount (script : Script) : Nat :=
  (script.map ScriptElement.executedOpCharge).sum

theorem executedOpCount_cons (element : ScriptElement) (rest : Script) :
    executedOpCount (element :: rest) =
      element.executedOpCharge + executedOpCount rest := by
  simp [executedOpCount]

theorem executedOpCount_sublist {selected script : Script}
    (sub : selected.Sublist script) :
    executedOpCount selected ≤ executedOpCount script := by
  induction sub <;> simp_all [executedOpCount] <;> omega

/-- Public keys one BASE or witness-v0 step adds to the operation count: the
    decoded key count of an active multisignature, zero otherwise. -/
def stepChargedKeys (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) : Nat :=
  match element with
  | .op opcode =>
      if ctx.sigVersion = .tapscript then 0
      else match opcodeKeyCount opcode flags (state.conditions.all id) state.stack with
        | .ok keys => keys
        | .error _ => 0
  | _ => 0

/-- The decoded multisignature frame fixes the same key count that
    `multisigKeyCount` reads from the frame's first element. -/
theorem multisigKeyCount_eq_pubkeys_length {flags : ScriptFlags} {stack : Stack}
    {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperands flags stack = .ok operands) :
    multisigKeyCount flags stack = .ok operands.pubkeys.length := by
  cases stack with
  | nil => simp [decodeCheckMultiSigOperands, bind, Except.bind] at decoded
  | cons countBytes rest =>
      unfold decodeCheckMultiSigOperands at decoded
      simp only [bind, Except.bind] at decoded
      cases number : decodeScriptNum countBytes flags.minimalData
          maxArithmeticScriptNumBytes with
      | error => simp [number] at decoded
      | ok value =>
          simp only [number] at decoded
          split at decoded
          · contradiction
          · rename_i notNegative
            split at decoded
            · contradiction
            · rename_i notLarge
              split at decoded
              · contradiction
              · rename_i longEnough
                cases dropped : rest.drop value.toNat with
                | nil => simp [dropped] at decoded
                | cons sigCountBytes afterSignatureCount =>
                    simp only [dropped] at decoded
                    cases sigNumber : decodeScriptNum sigCountBytes flags.minimalData
                        maxArithmeticScriptNumBytes with
                    | error => simp [sigNumber] at decoded
                    | ok sigValue =>
                        simp only [sigNumber] at decoded
                        split at decoded
                        · contradiction
                        · split at decoded
                          · contradiction
                          · split at decoded
                            · contradiction
                            · rename_i sigsLongEnough
                              split at decoded <;>
                                simp only [Except.ok.injEq] at decoded <;>
                                subst decoded <;>
                              · simp only [multisigKeyCount, bind, Except.bind, pure,
                                  Except.pure, number]
                                rw [if_neg (not_or.mpr ⟨notNegative, notLarge⟩)]
                                simp only [Except.ok.injEq, List.length_take]
                                omega

/-- A successful charge adds exactly the element's executed charge plus the
    decoded active-multisignature keys. -/
theorem chargeOperations_executed_delta {element : ScriptElement}
    {state charged : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (charging : chargeOperations element state flags ctx = .ok charged) :
    charged.operationCount = state.operationCount + element.executedOpCharge +
      stepChargedKeys element state flags ctx := by
  cases element with
  | op opcode =>
      simp only [chargeOperations, if_neg nontap] at charging
      cases counted : chargedOperationCount opcode state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging
          simp only [Except.map, Except.ok.injEq] at charging
          obtain ⟨keys, decoded, totalEq, _⟩ := chargedOperationCount_ok counted
          rw [← charging]
          simp only [ScriptElement.executedOpCharge, stepChargedKeys, if_neg nontap,
            decoded]
          omega
  | badOpcode opcode =>
      by_cases skip : ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60
      · have small : opcode.byte.toNat ≤ 0x60 := by
          rcases skip with tap | small
          · exact absurd tap nontap
          · exact small
        simp only [chargeOperations, if_pos skip, Except.ok.injEq] at charging
        rw [← charging]
        simp [ScriptElement.executedOpCharge, small, stepChargedKeys]
      · have big : ¬ opcode.byte.toNat ≤ 0x60 := fun small => skip (.inr small)
        simp only [chargeOperations, if_neg skip] at charging
        split at charging
        · cases charging
        · simp only [Except.ok.injEq] at charging
          rw [← charging]
          simp [ScriptElement.executedOpCharge, big, stepChargedKeys]
  | illegalOpcode _ =>
      simp only [chargeOperations, if_neg nontap] at charging
      split at charging
      · cases charging
      · simp only [Except.ok.injEq] at charging
        rw [← charging]
        simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | codeSeparator _ =>
      simp only [chargeOperations, if_neg nontap] at charging
      split at charging
      · cases charging
      · simp only [Except.ok.injEq] at charging
        rw [← charging]
        simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | pushData _ | pushNum _ | nonminimalPush _ | truncatedPush _ =>
      simp only [chargeOperations, Except.ok.injEq] at charging
      rw [← charging]
      first
        | (simp [ScriptElement.executedOpCharge, stepChargedKeys]; done)
        | rfl

/-- A higher starting count keeps a successful charge, adding exactly the
    element's executed charge and decoded keys. -/
theorem chargeOperations_raise_executed {element : ScriptElement}
    {state charged : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {count : Nat}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (charging : chargeOperations element state flags ctx = .ok charged)
    (fits : count + element.executedOpCharge + stepChargedKeys element state flags ctx ≤
      maxOpsPerScript) :
    chargeOperations element { state with operationCount := count } flags ctx =
      .ok ({ charged with
        operationCount := count + element.executedOpCharge +
          stepChargedKeys element state flags ctx }) := by
  cases element with
  | op opcode =>
      simp only [chargeOperations, if_neg nontap] at charging ⊢
      cases counted : chargedOperationCount opcode state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging
          simp only [Except.map, Except.ok.injEq] at charging
          obtain ⟨keys, decoded, totalEq, _⟩ := chargedOperationCount_ok counted
          have keysEq : stepChargedKeys (.op opcode) state flags ctx = keys := by
            simp [stepChargedKeys, if_neg nontap, decoded]
          rw [keysEq] at fits ⊢
          simp only [ScriptElement.executedOpCharge] at fits
          rw [chargedOperationCount_of_keys
            (state := { state with operationCount := count }) decoded (by simp only; omega)]
          simp only [Except.map, Except.ok.injEq]
          rw [← charging]
          simp [ScriptElement.executedOpCharge]
  | badOpcode opcode =>
      by_cases skip : ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60
      · have small : opcode.byte.toNat ≤ 0x60 := by
          rcases skip with tap | small
          · exact absurd tap nontap
          · exact small
        simp only [chargeOperations, if_pos skip, Except.ok.injEq] at charging ⊢
        rw [← charging]
        simp [ScriptElement.executedOpCharge, small, stepChargedKeys]
      · have big : ¬ opcode.byte.toNat ≤ 0x60 := fun small => skip (.inr small)
        simp only [chargeOperations, if_neg skip] at charging ⊢
        have fits' : ¬ count + 1 > maxOpsPerScript := by
          simp [ScriptElement.executedOpCharge, big, stepChargedKeys] at fits
          omega
        rw [if_neg fits']
        split at charging
        · cases charging
        · simp only [Except.ok.injEq] at charging ⊢
          rw [← charging]
          simp [ScriptElement.executedOpCharge, big, stepChargedKeys]
  | illegalOpcode _ =>
      simp only [chargeOperations, if_neg nontap] at charging ⊢
      have fits' : ¬ count + 1 > maxOpsPerScript := by
        simp [ScriptElement.executedOpCharge, stepChargedKeys] at fits
        omega
      rw [if_neg fits']
      split at charging
      · cases charging
      · simp only [Except.ok.injEq] at charging ⊢
        rw [← charging]
        simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | codeSeparator _ =>
      simp only [chargeOperations, if_neg nontap] at charging ⊢
      have fits' : ¬ count + 1 > maxOpsPerScript := by
        simp [ScriptElement.executedOpCharge, stepChargedKeys] at fits
        omega
      rw [if_neg fits']
      split at charging
      · cases charging
      · simp only [Except.ok.injEq] at charging ⊢
        rw [← charging]
        simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | pushData _ | pushNum _ | nonminimalPush _ | truncatedPush _ =>
      simp only [chargeOperations, Except.ok.injEq] at charging ⊢
      rw [← charging]
      simp [ScriptElement.executedOpCharge, stepChargedKeys]

/-- An inactive step charges only the element's executed charge. -/
theorem chargeOperations_inactive_executed {element : ScriptElement}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (inactive : state.conditions.all id = false)
    (fits : state.operationCount + element.executedOpCharge ≤ maxOpsPerScript) :
    ∃ count, state.operationCount ≤ count ∧
      count = state.operationCount + element.executedOpCharge ∧
      chargeOperations element state flags ctx =
        .ok { state with operationCount := count } := by
  cases element with
  | op opcode =>
      have quiet : opcodeKeyCount opcode flags (state.conditions.all id) state.stack =
          .ok 0 := by
        rw [inactive]
        cases opcode <;> rfl
      refine ⟨state.operationCount + 1, by omega, rfl, ?_⟩
      simp only [chargeOperations, if_neg nontap]
      rw [chargedOperationCount_of_keys quiet (by
        simp [ScriptElement.executedOpCharge] at fits; omega)]
      rfl
  | badOpcode opcode =>
      by_cases skip : ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60
      · have small : opcode.byte.toNat ≤ 0x60 := by
          rcases skip with tap | small
          · exact absurd tap nontap
          · exact small
        exact ⟨state.operationCount, by omega,
          by simp [ScriptElement.executedOpCharge, small],
          by simp [chargeOperations, skip]⟩
      · have big : ¬ opcode.byte.toNat ≤ 0x60 := fun small => skip (.inr small)
        refine ⟨state.operationCount + 1, by omega,
          by simp [ScriptElement.executedOpCharge, big], ?_⟩
        simp only [chargeOperations, if_neg skip]
        have fits' : ¬ state.operationCount + 1 > maxOpsPerScript := by
          simp [ScriptElement.executedOpCharge, big] at fits
          omega
        rw [if_neg fits']
  | illegalOpcode _ =>
      refine ⟨state.operationCount + 1, by omega, rfl, ?_⟩
      simp only [chargeOperations, if_neg nontap]
      rw [if_neg (by simp [ScriptElement.executedOpCharge] at fits; omega)]
  | codeSeparator _ =>
      refine ⟨state.operationCount + 1, by omega, rfl, ?_⟩
      simp only [chargeOperations, if_neg nontap]
      rw [if_neg (by simp [ScriptElement.executedOpCharge] at fits; omega)]
  | pushData _ | pushNum _ | nonminimalPush _ | truncatedPush _ =>
      exact ⟨state.operationCount, Nat.le_refl _, rfl, rfl⟩

/-- Keys charged along a successful runtime run: the decoded key counts of the
    active multisignature steps. Erroring runs are assigned zero. -/
def runKeys (oracle : CryptoOracle) : Script → RuntimeState → ScriptFlags →
    TxContext → Nat
  | [], _, _, _ => 0
  | element :: rest, state, flags, ctx =>
      match runtimeStep oracle element state flags ctx with
      | .error _ => 0
      | .ok next => stepChargedKeys element state flags ctx +
          runKeys oracle rest next flags ctx

@[simp] theorem runKeys_nil (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    runKeys oracle [] state flags ctx = 0 := rfl

theorem runKeys_cons {oracle : CryptoOracle} {element : ScriptElement}
    {rest : Script} {state next : RuntimeState} {flags : ScriptFlags}
    {ctx : TxContext}
    (stepped : runtimeStep oracle element state flags ctx = .ok next) :
    runKeys oracle (element :: rest) state flags ctx =
      stepChargedKeys element state flags ctx + runKeys oracle rest next flags ctx := by
  simp [runKeys, stepped]

/-- The charged keys do not read the operation count. -/
theorem stepChargedKeys_operationCount (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (count : Nat) :
    stepChargedKeys element { state with operationCount := count } flags ctx =
      stepChargedKeys element state flags ctx := by
  cases element <;> rfl

/-- Starting from a higher operation count keeps every successful result while
    the whole run's executed charge still fits, and charges the same keys. -/
theorem evaluateRuntime_raise_executed {oracle : CryptoOracle} {script : Script}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight count : Nat}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (success : evaluateRuntime oracle script state flags ctx = .success stack alt weight)
    (fits : count + executedOpCount script + runKeys oracle script state flags ctx ≤
      maxOpsPerScript) :
    evaluateRuntime oracle script { state with operationCount := count } flags ctx =
      .success stack alt weight ∧
    runKeys oracle script { state with operationCount := count } flags ctx =
      runKeys oracle script state flags ctx := by
  induction script generalizing state count with
  | nil => exact ⟨by simpa [evaluateRuntime, finishRuntime] using success, rfl⟩
  | cons element rest ih =>
      rw [executedOpCount_cons] at fits
      simp only [evaluateRuntime] at success
      cases stepped : runtimeStep oracle element state flags ctx with
      | error error => simp [stepped] at success
      | ok next =>
          simp only [stepped] at success
          obtain ⟨charged, charging, instruction⟩ := runtimeStep_ok stepped
          have keysCons := runKeys_cons (rest := rest) stepped
          rw [keysCons] at fits
          have headFits : count + element.executedOpCharge +
              stepChargedKeys element state flags ctx ≤ maxOpsPerScript := by omega
          have charging' := chargeOperations_raise_executed nontap charging headFits
          have moved := runtimeInstruction_operationCount oracle element
            { state with operationCount := charged } flags ctx
            (count + element.executedOpCharge + stepChargedKeys element state flags ctx)
          rw [instruction] at moved
          simp only [Except.map] at moved
          have nextStep : runtimeStep oracle element
              { state with operationCount := count } flags ctx =
              .ok ({ next with operationCount := count + element.executedOpCharge +
                stepChargedKeys element state flags ctx }) := by
            simp only [runtimeStep_withoutScriptCode, charging', Except.bind]
            exact moved
          have tailFits : count + element.executedOpCharge +
              stepChargedKeys element state flags ctx + executedOpCount rest +
              runKeys oracle rest next flags ctx ≤ maxOpsPerScript := by omega
          obtain ⟨completed, keysSame⟩ := ih success tailFits
          refine ⟨?_, ?_⟩
          · simp only [evaluateRuntime]
            rw [nextStep]
            exact completed
          · rw [runKeys_cons (rest := rest) nextStep, stepChargedKeys_operationCount, keysSame, keysCons]

/-- Inactive steps charge no multisignature keys. -/
theorem stepChargedKeys_eq_zero_of_inactive {element : ScriptElement}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (inactive : state.conditions.all id = false) :
    stepChargedKeys element state flags ctx = 0 := by
  cases element with
  | op opcode =>
      have quiet : opcodeKeyCount opcode flags false state.stack = .ok 0 := by
        cases opcode <;> rfl
      simp only [stepChargedKeys, inactive]
      split
      · rfl
      · rw [quiet]
  | _ => rfl

/-- Charged keys depend on activeness and the stack, not on the exact
    condition list. -/
theorem stepChargedKeys_conditions {element : ScriptElement} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} (conditions : List Bool)
    (active : conditions.all id = state.conditions.all id) :
    stepChargedKeys element { state with conditions := conditions } flags ctx =
      stepChargedKeys element state flags ctx := by
  cases element with
  | op opcode => simp only [stepChargedKeys, active]
  | _ => rfl

/-- A successful charge under the executed accounting, constructed from the
    decoded key count of the element. -/
theorem chargeOperations_executed_ok {element : ScriptElement} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (decoded : ∀ opcode, element = .op opcode → ∃ keys,
      opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok keys)
    (fits : state.operationCount + element.executedOpCharge +
        stepChargedKeys element state flags ctx ≤ maxOpsPerScript) :
    chargeOperations element state flags ctx =
      .ok ({ state with operationCount := state.operationCount +
        element.executedOpCharge + stepChargedKeys element state flags ctx }) := by
  cases element with
  | op opcode =>
      obtain ⟨keys, count⟩ := decoded opcode rfl
      have keysEq : stepChargedKeys (.op opcode) state flags ctx = keys := by
        simp [stepChargedKeys, nontap, count]
      simp only [chargeOperations, if_neg nontap, keysEq]
      rw [chargedOperationCount_of_keys count (by
        simp only [ScriptElement.executedOpCharge] at fits; omega)]
      rfl
  | badOpcode opcode =>
      by_cases small : opcode.byte.toNat ≤ 0x60
      · simp only [chargeOperations, if_pos (Or.inr small), Except.ok.injEq]
        simp [ScriptElement.executedOpCharge, small, stepChargedKeys]
      · have skip : ¬ (ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60) :=
          fun h => h.elim nontap small
        simp only [chargeOperations, if_neg skip]
        have fits' : ¬ state.operationCount + 1 > maxOpsPerScript := by
          simp [ScriptElement.executedOpCharge, small, stepChargedKeys] at fits
          omega
        rw [if_neg fits']
        simp [ScriptElement.executedOpCharge, small, stepChargedKeys]
  | illegalOpcode _ =>
      simp only [chargeOperations, if_neg nontap]
      have fits' : ¬ state.operationCount + 1 > maxOpsPerScript := by
        simp [ScriptElement.executedOpCharge, stepChargedKeys] at fits
        omega
      rw [if_neg fits']
      simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | codeSeparator _ =>
      simp only [chargeOperations, if_neg nontap]
      have fits' : ¬ state.operationCount + 1 > maxOpsPerScript := by
        simp [ScriptElement.executedOpCharge, stepChargedKeys] at fits
        omega
      rw [if_neg fits']
      simp [ScriptElement.executedOpCharge, stepChargedKeys]
  | pushData _ | pushNum _ | nonminimalPush _ | truncatedPush _ =>
      simp [chargeOperations, ScriptElement.executedOpCharge, stepChargedKeys]

/-- On an active successful step the observed multisignature key charge is
    exactly the runtime's decoded key charge. -/
theorem executedMultiSigKeyCharge_eq_stepChargedKeys {element : ScriptElement}
    {state : RuntimeState} {nextStack nextAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (nontap : ctx.sigVersion ≠ .tapscript)
    (active : state.conditions.all id = true)
    (evaluated : Eval [element] state.stack state.altStack flags ctx
      (.success nextStack nextAlt)) :
    executedMultiSigKeyCharge element state.stack flags ctx =
      stepChargedKeys element state flags ctx := by
  cases element with
  | op opcode =>
      obtain ⟨stack, altStack, conditions, weight, count⟩ := state
      have activeTrue : conditions.all id = true := by simpa using active
      cases opcode
      case OP_CHECKMULTISIG | OP_CHECKMULTISIGVERIFY =>
        cases evaluated <;> try simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]
        all_goals
          obtain ⟨operands, decodedFor⟩ : ∃ operands,
              decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands :=
            ⟨_, by assumption⟩
          have decoded : decodeCheckMultiSigOperands flags stack = .ok operands := by
            simpa [decodeCheckMultiSigOperandsFor, nontap] using decodedFor
          have keyCount := multisigKeyCount_eq_pubkeys_length decoded
          first
            | rw [executedMultiSigKeyCharge_checkmultisig decodedFor]
            | rw [executedMultiSigKeyCharge_checkmultisigverify decodedFor]
          simp only [stepChargedKeys, if_neg nontap, opcodeKeyCount, activeTrue,
            ↓reduceIte, keyCount]
      all_goals
        first
        | rfl
        | (rw [executedMultiSigKeyCharge_eq_zero_of_opcode_ne (by decide) (by decide)]
           simp [stepChargedKeys, nontap, opcodeKeyCount])
  | _ => rfl

/-- Outside Tapscript no instruction debits validation weight, so an observed
    execution has zero signature weight. -/
theorem EvalResources.signatureWeight_eq_zero_of_nontap
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources)
    (nontap : ctx.sigVersion ≠ .tapscript) : resources.signatureWeight = 0 := by
  induction observed with
  | empty => rfl
  | step head tail ih =>
      rename_i element rest stack alt nextStack nextAlt finalStack finalAlt flags ctx tailResources
      have zero : executedSignatureWeight element stack ctx = 0 := by
        simp [executedSignatureWeight, nontap]
      simp only [ExecutionResources.prepend_signatureWeight, zero, ih nontap]
  | if_execute split minimal selected ih => simpa using ih nontap
  | notif_execute split minimal selected ih => simpa using ih nontap

/-- A decoded multisignature frame fits in the initial stack with room to
    spare: the frame holds the two counts, the public keys, the signatures (at
    most one per key), and at most one dummy item above `rest`. -/
theorem decodeCheckMultiSigOperandsFor_length_le {flags : ScriptFlags}
    {ctx : TxContext} {stack : Stack} {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands) :
    stack.length ≤ operands.rest.length + 3 + 2 * operands.pubkeys.length := by
  unfold decodeCheckMultiSigOperandsFor at decoded
  split at decoded
  · contradiction
  · cases stack with
    | nil => simp [decodeCheckMultiSigOperands, bind, Except.bind] at decoded
    | cons countBytes rest =>
        unfold decodeCheckMultiSigOperands at decoded
        simp only [bind, Except.bind] at decoded
        cases number : decodeScriptNum countBytes flags.minimalData
            maxArithmeticScriptNumBytes with
        | error => simp [number] at decoded
        | ok value =>
            simp only [number] at decoded
            split at decoded
            · contradiction
            · rename_i notNegative
              split at decoded
              · contradiction
              · rename_i notLarge
                split at decoded
                · contradiction
                · rename_i longEnough
                  cases dropped : rest.drop value.toNat with
                  | nil => simp [dropped] at decoded
                  | cons sigCountBytes afterSignatureCount =>
                      simp only [dropped] at decoded
                      cases sigNumber : decodeScriptNum sigCountBytes
                          flags.minimalData maxArithmeticScriptNumBytes with
                      | error => simp [sigNumber] at decoded
                      | ok sigValue =>
                          simp only [sigNumber] at decoded
                          split at decoded
                          · contradiction
                          · rename_i sigNotNegative
                            split at decoded
                            · contradiction
                            · rename_i sigsBounded
                              split at decoded
                              · contradiction
                              · rename_i sigsLongEnough
                                have keyLength := congrArg List.length dropped
                                have pubkeysLength :
                                    (rest.take value.toNat).length = value.toNat := by
                                  simp only [List.length_take]
                                  omega
                                cases sigFrame :
                                    afterSignatureCount.drop sigValue.toNat with
                                | nil =>
                                    simp only [sigFrame] at decoded
                                    simp only [Except.ok.injEq] at decoded
                                    subst decoded
                                    have sigLength := congrArg List.length sigFrame
                                    simp only [List.length_drop, List.length_cons] at keyLength
                                    simp only [List.length_drop, List.length_nil] at sigLength
                                    simp only [List.length_cons, List.length_nil,
                                      pubkeysLength]
                                    omega
                                | cons dummy tail =>
                                    simp only [sigFrame] at decoded
                                    simp only [Except.ok.injEq] at decoded
                                    subst decoded
                                    have sigLength := congrArg List.length sigFrame
                                    simp only [List.length_drop, List.length_cons] at keyLength sigLength
                                    simp only [List.length_cons, pubkeysLength]
                                    omega

/-- A leading conditional delimiter cannot be the last source element. -/
private theorem absurd_splitConditional_nil {frame : ConditionalFrame}
    (split : splitConditional [] = some frame) : False := by
  nomatch split

/-- One successfully executed instruction drops at most three combined stack
    items plus twice the executed multisignature key charge. -/
theorem Eval.singleton_drop_le {element : ScriptElement}
    {stack alt nextStack nextAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval [element] stack alt flags ctx (.success nextStack nextAlt)) :
    stack.length + alt.length ≤ nextStack.length + nextAlt.length +
      3 * element.executedOpCharge +
        2 * executedMultiSigKeyCharge element stack flags ctx := by
  have noUnclosed (result : ExecResult) :
      finishUnclosedConditional result ≠ .success nextStack nextAlt := by
    cases result <;> simp [finishUnclosedConditional]
  generalize resultEq : ExecResult.success nextStack nextAlt = result at evaluated
  cases evaluated
  all_goals first
    | exact absurd resultEq.symm (noUnclosed _)
    | (exfalso
       apply absurd_splitConditional_nil
       assumption)
    | cases resultEq
  all_goals (try (rename_i inner; cases inner))
  all_goals first
    | (rename_i decoded
       have len := decodeCheckMultiSigOperandsFor_length_le decoded
       first
         | rw [executedMultiSigKeyCharge_checkmultisig decoded]
         | rw [executedMultiSigKeyCharge_checkmultisigverify decoded]
       simp only [ScriptElement.executedOpCharge, List.length_cons]
       omega)
    | (simp_all only [ScriptElement.executedOpCharge, List.length_cons,
        List.length_eraseIdx]; (try split) <;> omega)

/-- Bound the peak backwards from the final stacks by the maximum number of
    items that the remaining opcodes and multisignatures can remove. -/
theorem EvalResources.peakStackItems_le_final_add_operations
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources) :
    resources.peakStackItems ≤ finalStack.length + finalAlt.length +
      3 * executedOpCount script + 2 * resources.executedMultiSigKeys := by
  induction observed with
  | empty => simp [executedOpCount]
  | step head tail ih =>
      have drop := head.singleton_drop_le
      have initial := tail.initial_le_peak
      simp only [ExecutionResources.prepend_peakStackItems,
        ExecutionResources.prepend_executedMultiSigKeys, executedOpCount_cons]
      omega
  | @if_execute top rest altStack script frame flags ctx finalStack finalAlt selectedResources
      split minimal selected ih =>
      have initial := selected.initial_le_peak
      have projected : selectConditionalTail 0 (castToBool top) script =
          some (frame.select (castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := executedOpCount_sublist (selectConditionalTail_sublist projected)
      simp only [ExecutionResources.prepend_peakStackItems,
        ExecutionResources.prepend_executedMultiSigKeys, executedOpCount_cons,
        ScriptElement.executedOpCharge, List.length_cons]
      omega
  | @notif_execute top rest altStack script frame flags ctx finalStack finalAlt selectedResources
      split minimal selected ih =>
      have initial := selected.initial_le_peak
      have projected : selectConditionalTail 0 (!castToBool top) script =
          some (frame.select (!castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := executedOpCount_sublist (selectConditionalTail_sublist projected)
      simp only [ExecutionResources.prepend_peakStackItems,
        ExecutionResources.prepend_executedMultiSigKeys, executedOpCount_cons,
        ScriptElement.executedOpCharge, List.length_cons]
      omega

/-- A successful charge and instruction assemble into a successful step. -/
theorem runtimeStep_of_charge_execute {oracle : CryptoOracle} {element : ScriptElement}
    {state charged next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (charging : chargeOperations element state flags ctx = .ok charged)
    (executed : executeRuntimeElement oracle element charged flags ctx = .ok next)
    (bounded : next.stack.length + next.altStack.length ≤ maxStackSize) :
    runtimeStep oracle element state flags ctx = .ok next := by
  simp only [runtimeStep_withoutScriptCode, charging, bind, Except.bind, runtimeInstruction,
    executed]
  rw [checkRuntimeStack, if_neg (Nat.not_lt.mpr bounded)]

/-- An opcode with a zero decoded key count charges no multisignature keys. -/
theorem stepChargedKeys_eq_zero_of_quiet {opcode : Opcode} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (quiet : opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok 0) :
    stepChargedKeys (.op opcode) state flags ctx = 0 := by
  simp only [stepChargedKeys]
  split
  · rfl
  · rw [quiet]

private theorem map_cons_eq_some {source : Option Script} {element : ScriptElement}
    {selected : Script} (mapped : source.map (element :: ·) = some selected) :
    ∃ tail, source = some tail ∧ selected = element :: tail := by
  cases source with
  | none => simp at mapped
  | some tail => exact ⟨tail, rfl, (Option.some.inj mapped).symm⟩

/-- Restore one removed conditional to a successful projected execution under
executed-path operation accounting. Skipped instructions charge only their
executed charge; the active path charges its decoded multisignature keys, so
the source executed-op count plus the projected run's charged keys must fit.
The restored walk charges exactly the keys the projected run charges. -/
theorem runtime_restore_conditional_executed
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (script selected : Script) (state : RuntimeState)
    (nested outer : List Bool) (choice : Bool)
    (nontap : ctx.sigVersion ≠ .tapscript)
    (projected : selectConditionalTail nested.length choice script = some selected)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (legal : ∀ element ∈ script, element.isIllegalOpcode = false)
    (bounded : state.stack.length + state.altStack.length ≤ maxStackSize)
    (fits : state.operationCount + executedOpCount script +
        runKeys oracle selected
          { state with conditions := (if choice then nested else []) ++ outer } flags ctx ≤
        maxOpsPerScript)
    (success : evaluateRuntime oracle selected
      { state with conditions := (if choice then nested else []) ++ outer } flags ctx =
        .success stack alt weight) :
    evaluateRuntime oracle script
        { state with conditions := nested ++ choice :: outer } flags ctx =
        .success stack alt weight ∧
      runKeys oracle script { state with conditions := nested ++ choice :: outer } flags ctx =
        runKeys oracle selected
          { state with conditions := (if choice then nested else []) ++ outer } flags ctx := by
  induction script generalizing selected state nested outer choice with
  | nil => simp [selectConditionalTail] at projected
  | cons element rest ih =>
      have pushBound : ¬ element.pushSize > maxScriptElementSize :=
        Nat.not_lt.mpr (pushes element (by simp))
      have tailPushes : ∀ element ∈ rest, element.pushSize ≤ maxScriptElementSize :=
        fun element member => pushes element (by simp [member])
      have tailLegal : ∀ element ∈ rest, element.isIllegalOpcode = false :=
        fun element member => legal element (by simp [member])
      rw [executedOpCount_cons] at fits
      have ifNilGen : ∀ c : Bool, (if c then ([] : List Bool) else []) = [] :=
        fun c => by cases c <;> rfl
      by_cases ordinary : NonConditional element
      · cases choice with
        | false =>
            have tailProjected : selectConditionalTail nested.length false rest = some selected := by
              simpa [select_ordinary element ordinary] using projected
            have fitsN : state.operationCount + (element.executedOpCharge + executedOpCount rest) +
                runKeys oracle selected { state with conditions := [] ++ outer } flags ctx ≤
                maxOpsPerScript := fits
            have successN : evaluateRuntime oracle selected
                { state with conditions := [] ++ outer } flags ctx =
                .success stack alt weight := success
            obtain ⟨count, _, countEq, charging⟩ := chargeOperations_inactive_executed nontap
              (state := { state with conditions := nested ++ false :: outer })
              (by simp [List.all_append])
              (by show state.operationCount + element.executedOpCharge ≤ maxOpsPerScript; omega)
            have countEqN : count = state.operationCount + element.executedOpCharge := countEq
            have executed : executeRuntimeElement oracle element
                { state with operationCount := count, conditions := nested ++ false :: outer }
                flags ctx =
                .ok { state with operationCount := count, conditions := nested ++ false :: outer } := by
              simp [execute_ordinary element ordinary (legal element (by simp)), pushBound,
                List.all_append, pure, Except.pure]
            obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap successN
              (count := count)
              (by have sub := executedOpCount_sublist (selectConditionalTail_sublist tailProjected)
                  omega)
            have raisedRunN : evaluateRuntime oracle selected
                { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                .success stack alt weight := raisedRun
            have raisedKeysN : runKeys oracle selected
                { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                runKeys oracle selected { state with conditions := [] ++ outer } flags ctx :=
              raisedKeys
            obtain ⟨ihRun, ihKeys⟩ := ih selected { state with operationCount := count }
              nested outer false tailProjected tailPushes tailLegal bounded
              (by show count + executedOpCount rest +
                    runKeys oracle selected
                      { state with operationCount := count, conditions := [] ++ outer } flags ctx ≤
                    maxOpsPerScript
                  omega)
              raisedRunN
            have ihKeysN : runKeys oracle rest
                { state with operationCount := count, conditions := nested ++ false :: outer }
                flags ctx =
                runKeys oracle selected
                  { state with operationCount := count, conditions := [] ++ outer } flags ctx :=
              ihKeys
            refine ⟨?_, ?_⟩
            · exact runtime_cons_success charging executed bounded ihRun
            · have stepped : runtimeStep oracle element
                  { state with conditions := nested ++ false :: outer } flags ctx =
                  .ok ({ state with
                    operationCount := count
                    conditions := nested ++ false :: outer }) :=
                runtimeStep_of_charge_execute charging executed bounded
              have headZero : stepChargedKeys element
                  { state with conditions := nested ++ false :: outer } flags ctx = 0 :=
                stepChargedKeys_eq_zero_of_inactive (by simp [List.all_append])
              calc runKeys oracle (element :: rest)
                    { state with conditions := nested ++ false :: outer } flags ctx
                  = stepChargedKeys element
                      { state with conditions := nested ++ false :: outer } flags ctx +
                      runKeys oracle rest
                        { state with
                          operationCount := count
                          conditions := nested ++ false :: outer } flags ctx :=
                    runKeys_cons stepped
                _ = runKeys oracle selected { state with conditions := [] ++ outer } flags ctx := by
                    rw [headZero, Nat.zero_add, ihKeysN, raisedKeysN]
        | true =>
            obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
              (by simpa [select_ordinary element ordinary] using projected)
            have fitsN : state.operationCount + (element.executedOpCharge + executedOpCount rest) +
                runKeys oracle (element :: selectedTail)
                  { state with conditions := nested ++ outer } flags ctx ≤ maxOpsPerScript := fits
            have successN : evaluateRuntime oracle (element :: selectedTail)
                { state with conditions := nested ++ outer } flags ctx =
                .success stack alt weight := success
            obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
              runtime_success_cons successN
            obtain ⟨moved, conditions⟩ := ordinary_conditions (nested ++ true :: outer) ordinary
              (by simp [List.all_append]) executed
            have same : { next with conditions := nested ++ outer } = next := by
              cases next
              simp only at conditions
              cases conditions
              rfl
            have projNext : ({ next with conditions := (if true then nested else []) ++ outer } :
                RuntimeState) = next := same
            have steppedProj : runtimeStep oracle element
                { state with conditions := nested ++ outer } flags ctx = .ok next :=
              runtimeStep_of_charge_execute charging executed nextBound
            have deltaN : count = state.operationCount + element.executedOpCharge +
                stepChargedKeys element { state with conditions := nested ++ outer } flags ctx :=
              chargeOperations_executed_delta nontap charging
            have counted : next.operationCount = count :=
              executeRuntimeElement_operationCount_eq executed
            have fitsRest : next.operationCount + executedOpCount rest +
                runKeys oracle selectedTail next flags ctx ≤ maxOpsPerScript := by
              rw [runKeys_cons (rest := selectedTail) steppedProj] at fitsN
              omega
            obtain ⟨ihRun, ihKeys⟩ := ih selectedTail next nested outer true tailProjected
              tailPushes tailLegal nextBound
              (by rw [projNext]; exact fitsRest)
              (by rw [projNext]; exact tail)
            have ihKeysN : runKeys oracle rest
                { next with conditions := nested ++ true :: outer } flags ctx =
                runKeys oracle selectedTail next flags ctx := by
              rw [projNext] at ihKeys
              exact ihKeys
            have chargingWalk := chargeOperations_conditions
              (state := { state with conditions := nested ++ outer })
              (nested ++ true :: outer) (by simp [List.all_append]) charging
            refine ⟨?_, ?_⟩
            · exact runtime_cons_success chargingWalk moved nextBound ihRun
            · have steppedWalk : runtimeStep oracle element
                  { state with conditions := nested ++ true :: outer } flags ctx =
                  .ok { next with conditions := nested ++ true :: outer } :=
                runtimeStep_of_charge_execute chargingWalk moved nextBound
              have sckWalk : stepChargedKeys element
                  { state with conditions := nested ++ true :: outer } flags ctx =
                  stepChargedKeys element { state with conditions := nested ++ outer } flags ctx :=
                stepChargedKeys_conditions (state := { state with conditions := nested ++ outer })
                  (nested ++ true :: outer) (by simp [List.all_append])
              calc runKeys oracle (element :: rest)
                    { state with conditions := nested ++ true :: outer } flags ctx
                  = stepChargedKeys element
                      { state with conditions := nested ++ true :: outer } flags ctx +
                      runKeys oracle rest
                        { next with conditions := nested ++ true :: outer } flags ctx :=
                    runKeys_cons steppedWalk
                _ = stepChargedKeys element
                      { state with conditions := nested ++ true :: outer } flags ctx +
                      runKeys oracle selectedTail next flags ctx := by
                    rw [ihKeysN]
                _ = stepChargedKeys element
                      { state with conditions := nested ++ outer } flags ctx +
                      runKeys oracle selectedTail next flags ctx := by
                    rw [sckWalk]
                _ = runKeys oracle (element :: selectedTail)
                      { state with conditions := nested ++ outer } flags ctx :=
                    (runKeys_cons steppedProj).symm
      · by_cases branch : element.isBranch = true
        · cases choice with
          | false =>
              have tailProjected : selectConditionalTail (false :: nested).length false rest =
                  some selected := by
                simpa [select_branch element branch] using projected
              have fitsN : state.operationCount +
                  (element.executedOpCharge + executedOpCount rest) +
                  runKeys oracle selected { state with conditions := [] ++ outer } flags ctx ≤
                  maxOpsPerScript := fits
              have successN : evaluateRuntime oracle selected
                  { state with conditions := [] ++ outer } flags ctx =
                  .success stack alt weight := success
              obtain ⟨count, _, countEq, charging⟩ := chargeOperations_inactive_executed nontap
                (state := { state with conditions := nested ++ false :: outer })
                (by simp [List.all_append])
                (by show state.operationCount + element.executedOpCharge ≤ maxOpsPerScript; omega)
              have countEqN : count = state.operationCount + element.executedOpCharge := countEq
              have executed : executeRuntimeElement oracle element
                  { state with operationCount := count, conditions := nested ++ false :: outer }
                  flags ctx =
                  .ok ({ state with
                    operationCount := count
                    conditions := false :: (nested ++ false :: outer) }) := by
                simp [execute_branch element branch, List.all_append, pure, Except.pure]
              obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap successN
                (count := count)
                (by have sub := executedOpCount_sublist (selectConditionalTail_sublist tailProjected)
                    omega)
              have raisedRunN : evaluateRuntime oracle selected
                  { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                  .success stack alt weight := raisedRun
              have raisedKeysN : runKeys oracle selected
                  { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                  runKeys oracle selected { state with conditions := [] ++ outer } flags ctx :=
                raisedKeys
              obtain ⟨ihRun, ihKeys⟩ := ih selected { state with operationCount := count }
                (false :: nested) outer false tailProjected tailPushes tailLegal bounded
                (by show count + executedOpCount rest +
                      runKeys oracle selected
                        { state with operationCount := count, conditions := [] ++ outer } flags ctx ≤
                      maxOpsPerScript
                    omega)
                raisedRunN
              have ihKeysN : runKeys oracle rest
                  { state with
                    operationCount := count
                    conditions := false :: (nested ++ false :: outer) } flags ctx =
                  runKeys oracle selected
                    { state with operationCount := count, conditions := [] ++ outer } flags ctx :=
                ihKeys
              refine ⟨?_, ?_⟩
              · exact runtime_cons_success charging executed bounded ihRun
              · have stepped : runtimeStep oracle element
                    { state with conditions := nested ++ false :: outer } flags ctx =
                    .ok ({ state with
                      operationCount := count
                      conditions := false :: (nested ++ false :: outer) }) :=
                  runtimeStep_of_charge_execute charging executed bounded
                have headZero : stepChargedKeys element
                    { state with conditions := nested ++ false :: outer } flags ctx = 0 :=
                  stepChargedKeys_eq_zero_of_inactive (by simp [List.all_append])
                calc runKeys oracle (element :: rest)
                      { state with conditions := nested ++ false :: outer } flags ctx
                    = stepChargedKeys element
                        { state with conditions := nested ++ false :: outer } flags ctx +
                        runKeys oracle rest
                          { state with
                            operationCount := count
                            conditions := false :: (nested ++ false :: outer) } flags ctx :=
                      runKeys_cons stepped
                  _ = runKeys oracle selected { state with conditions := [] ++ outer } flags ctx := by
                      rw [headZero, Nat.zero_add, ihKeysN, raisedKeysN]
          | true =>
              obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                (by simpa [select_branch element branch] using projected)
              have fitsN : state.operationCount +
                  (element.executedOpCharge + executedOpCount rest) +
                  runKeys oracle (element :: selectedTail)
                    { state with conditions := nested ++ outer } flags ctx ≤ maxOpsPerScript := fits
              have successN : evaluateRuntime oracle (element :: selectedTail)
                  { state with conditions := nested ++ outer } flags ctx =
                  .success stack alt weight := success
              obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                runtime_success_cons successN
              obtain ⟨inner, conditions, moved⟩ := branch_conditions (nested ++ true :: outer) branch
                (by simp [List.all_append]) executed
              have same : { next with conditions := (inner :: nested) ++ outer } = next := by
                cases next
                simp only at conditions
                cases conditions
                rfl
              have projNext : ({ next with
                    conditions := (if true then inner :: nested else []) ++ outer } :
                  RuntimeState) = next := same
              have steppedProj : runtimeStep oracle element
                  { state with conditions := nested ++ outer } flags ctx = .ok next :=
                runtimeStep_of_charge_execute charging executed nextBound
              have deltaN : count = state.operationCount + element.executedOpCharge +
                  stepChargedKeys element { state with conditions := nested ++ outer } flags ctx :=
                chargeOperations_executed_delta nontap charging
              have counted : next.operationCount = count :=
                executeRuntimeElement_operationCount_eq executed
              have fitsRest : next.operationCount + executedOpCount rest +
                  runKeys oracle selectedTail next flags ctx ≤ maxOpsPerScript := by
                rw [runKeys_cons (rest := selectedTail) steppedProj] at fitsN
                omega
              obtain ⟨ihRun, ihKeys⟩ := ih selectedTail next (inner :: nested) outer true
                (by simpa using tailProjected) tailPushes tailLegal nextBound
                (by rw [projNext]; exact fitsRest)
                (by rw [projNext]; exact tail)
              have ihKeysN : runKeys oracle rest
                  { next with conditions := inner :: (nested ++ true :: outer) } flags ctx =
                  runKeys oracle selectedTail next flags ctx := by
                rw [projNext] at ihKeys
                exact ihKeys
              have chargingWalk := chargeOperations_conditions
                (state := { state with conditions := nested ++ outer })
                (nested ++ true :: outer) (by simp [List.all_append]) charging
              refine ⟨?_, ?_⟩
              · exact runtime_cons_success chargingWalk moved nextBound ihRun
              · have steppedWalk : runtimeStep oracle element
                    { state with conditions := nested ++ true :: outer } flags ctx =
                    .ok { next with conditions := inner :: (nested ++ true :: outer) } :=
                  runtimeStep_of_charge_execute chargingWalk moved nextBound
                have sckWalk : stepChargedKeys element
                    { state with conditions := nested ++ true :: outer } flags ctx =
                    stepChargedKeys element { state with conditions := nested ++ outer } flags ctx :=
                  stepChargedKeys_conditions (state := { state with conditions := nested ++ outer })
                    (nested ++ true :: outer) (by simp [List.all_append])
                calc runKeys oracle (element :: rest)
                      { state with conditions := nested ++ true :: outer } flags ctx
                    = stepChargedKeys element
                        { state with conditions := nested ++ true :: outer } flags ctx +
                        runKeys oracle rest
                          { next with conditions := inner :: (nested ++ true :: outer) } flags ctx :=
                      runKeys_cons steppedWalk
                  _ = stepChargedKeys element
                        { state with conditions := nested ++ true :: outer } flags ctx +
                        runKeys oracle selectedTail next flags ctx := by
                      rw [ihKeysN]
                  _ = stepChargedKeys element
                        { state with conditions := nested ++ outer } flags ctx +
                        runKeys oracle selectedTail next flags ctx := by
                      rw [sckWalk]
                  _ = runKeys oracle (element :: selectedTail)
                        { state with conditions := nested ++ outer } flags ctx :=
                      (runKeys_cons steppedProj).symm
        · cases element with
          | pushData => exact False.elim (ordinary trivial)
          | pushNum => exact False.elim (ordinary trivial)
          | badOpcode => exact False.elim (ordinary trivial)
          | illegalOpcode => exact False.elim (ordinary trivial)
          | nonminimalPush => exact False.elim (ordinary trivial)
          | truncatedPush => exact False.elim (ordinary trivial)
          | codeSeparator => exact False.elim (ordinary trivial)
          | op opcode =>
              cases opcode <;> simp only [NonConditional, ScriptElement.isBranch] at ordinary branch
              case OP_ELSE =>
                cases nested with
                | nil =>
                    have tailSub := selectConditionalTail_sublist (script := rest) (depth := 0)
                      (choice := !choice) projected
                    have fitsN : state.operationCount +
                        ((ScriptElement.op .OP_ELSE).executedOpCharge + executedOpCount rest) +
                        runKeys oracle selected { state with conditions := outer } flags ctx ≤
                        maxOpsPerScript := by
                      have fits' := fits
                      simp only [ifNilGen, List.nil_append] at fits'
                      exact fits'
                    have successN : evaluateRuntime oracle selected
                        { state with conditions := outer } flags ctx =
                        .success stack alt weight := by
                      have success' := success
                      simp only [ifNilGen, List.nil_append] at success'
                      exact success'
                    have eocElse : (ScriptElement.op .OP_ELSE).executedOpCharge = 1 := rfl
                    have sckElse : stepChargedKeys (.op .OP_ELSE)
                        { state with conditions := [] ++ choice :: outer } flags ctx = 0 :=
                      stepChargedKeys_eq_zero_of_quiet rfl
                    have charging : chargeOperations (.op .OP_ELSE)
                        { state with conditions := [] ++ choice :: outer } flags ctx =
                        .ok ({ state with
                          operationCount := state.operationCount + 1
                          conditions := [] ++ choice :: outer }) := by
                      simpa only [ScriptElement.executedOpCharge, stepChargedKeys_eq_zero_of_quiet (opcode := .OP_ELSE) rfl, Nat.add_zero] using
                        chargeOperations_executed_ok (element := .op .OP_ELSE) nontap
                          (state := { state with conditions := [] ++ choice :: outer })
                          (fun _ same => by cases same; exact ⟨0, rfl⟩)
                          (by rw [sckElse]
                              show state.operationCount + 1 + 0 ≤ maxOpsPerScript
                              omega)
                    have executed : executeRuntimeElement oracle (.op .OP_ELSE)
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := [] ++ choice :: outer } flags ctx =
                        .ok ({ state with
                          operationCount := state.operationCount + 1
                          conditions := (!choice) :: outer }) := by
                      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap successN
                      (count := state.operationCount + 1)
                      (by have sub := executedOpCount_sublist tailSub
                          omega)
                    have raisedRunN : evaluateRuntime oracle selected
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := outer } flags ctx =
                        .success stack alt weight := raisedRun
                    have raisedKeysN : runKeys oracle selected
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := outer } flags ctx =
                        runKeys oracle selected { state with conditions := outer } flags ctx :=
                      raisedKeys
                    obtain ⟨ihRun, ihKeys⟩ := ih selected
                      { state with operationCount := state.operationCount + 1 } [] outer (!choice)
                      projected tailPushes tailLegal bounded
                      (by rw [ifNilGen (!choice), List.nil_append]
                          show state.operationCount + 1 + executedOpCount rest +
                            runKeys oracle selected
                              { state with
                                operationCount := state.operationCount + 1
                                conditions := outer } flags ctx ≤ maxOpsPerScript
                          omega)
                      (by rw [ifNilGen (!choice), List.nil_append]; exact raisedRunN)
                    have ihKeysN : runKeys oracle rest
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := (!choice) :: outer } flags ctx =
                        runKeys oracle selected
                          { state with
                            operationCount := state.operationCount + 1
                            conditions := outer } flags ctx := by
                      have ihKeys' := ihKeys
                      rw [ifNilGen (!choice), List.nil_append] at ihKeys'
                      exact ihKeys'
                    refine ⟨?_, ?_⟩
                    · exact runtime_cons_success charging executed bounded ihRun
                    · have stepped : runtimeStep oracle (.op .OP_ELSE)
                          { state with conditions := [] ++ choice :: outer } flags ctx =
                          .ok ({ state with
                            operationCount := state.operationCount + 1
                            conditions := (!choice) :: outer }) :=
                        runtimeStep_of_charge_execute charging executed bounded
                      have goalN : runKeys oracle (.op .OP_ELSE :: rest)
                            { state with conditions := [] ++ choice :: outer } flags ctx =
                            runKeys oracle selected { state with conditions := outer } flags ctx := by
                        calc runKeys oracle (.op .OP_ELSE :: rest)
                              { state with conditions := [] ++ choice :: outer } flags ctx
                            = stepChargedKeys (.op .OP_ELSE)
                                { state with conditions := [] ++ choice :: outer } flags ctx +
                                runKeys oracle rest
                                  { state with
                                    operationCount := state.operationCount + 1
                                    conditions := (!choice) :: outer } flags ctx :=
                              runKeys_cons stepped
                          _ = runKeys oracle selected
                                { state with
                                  operationCount := state.operationCount + 1
                                  conditions := outer } flags ctx := by
                              rw [sckElse, Nat.zero_add, ihKeysN]
                          _ = runKeys oracle selected { state with conditions := outer } flags ctx :=
                              raisedKeysN
                      simpa only [ifNilGen, List.nil_append] using goalN
                | cons inner nested =>
                    cases choice with
                    | false =>
                        have tailProjected : selectConditionalTail ((!inner) :: nested).length false
                            rest = some selected := by
                          simpa [selectConditionalTail] using projected
                        have fitsN : state.operationCount +
                            ((ScriptElement.op .OP_ELSE).executedOpCharge + executedOpCount rest) +
                            runKeys oracle selected { state with conditions := [] ++ outer } flags ctx ≤
                            maxOpsPerScript := fits
                        have successN : evaluateRuntime oracle selected
                            { state with conditions := [] ++ outer } flags ctx =
                            .success stack alt weight := success
                        have eocElse : (ScriptElement.op .OP_ELSE).executedOpCharge = 1 := rfl
                        obtain ⟨count, _, countEq, charging⟩ := chargeOperations_inactive_executed
                          (element := .op .OP_ELSE) nontap
                          (state := { state with conditions := (inner :: nested) ++ false :: outer })
                          (by simp [List.all_append])
                          (by show state.operationCount + 1 ≤ maxOpsPerScript; omega)
                        have countEqN : count = state.operationCount + 1 := by
                          have countEq' := countEq
                          rw [eocElse] at countEq'
                          exact countEq'
                        have executed : executeRuntimeElement oracle (.op .OP_ELSE)
                            { state with
                              operationCount := count
                              conditions := (inner :: nested) ++ false :: outer } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := (!inner) :: (nested ++ false :: outer) }) := by
                          simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap
                          successN (count := count)
                          (by have sub := executedOpCount_sublist
                                (selectConditionalTail_sublist tailProjected)
                              omega)
                        have raisedRunN : evaluateRuntime oracle selected
                            { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                            .success stack alt weight := raisedRun
                        have raisedKeysN : runKeys oracle selected
                            { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                            runKeys oracle selected { state with conditions := [] ++ outer } flags ctx :=
                          raisedKeys
                        obtain ⟨ihRun, ihKeys⟩ := ih selected { state with operationCount := count }
                          ((!inner) :: nested) outer false tailProjected tailPushes tailLegal bounded
                          (by show count + executedOpCount rest +
                                runKeys oracle selected
                                  { state with
                                    operationCount := count
                                    conditions := [] ++ outer } flags ctx ≤ maxOpsPerScript
                              omega)
                          raisedRunN
                        have ihKeysN : runKeys oracle rest
                            { state with
                              operationCount := count
                              conditions := (!inner) :: (nested ++ false :: outer) } flags ctx =
                            runKeys oracle selected
                              { state with operationCount := count, conditions := [] ++ outer } flags ctx :=
                          ihKeys
                        refine ⟨?_, ?_⟩
                        · exact runtime_cons_success charging executed bounded ihRun
                        · have stepped : runtimeStep oracle (.op .OP_ELSE)
                              { state with conditions := (inner :: nested) ++ false :: outer } flags ctx =
                              .ok ({ state with
                                operationCount := count
                                conditions := (!inner) :: (nested ++ false :: outer) }) :=
                            runtimeStep_of_charge_execute charging executed bounded
                          have headZero : stepChargedKeys (.op .OP_ELSE)
                              { state with conditions := (inner :: nested) ++ false :: outer } flags ctx = 0 :=
                            stepChargedKeys_eq_zero_of_quiet rfl
                          calc runKeys oracle (.op .OP_ELSE :: rest)
                                { state with conditions := (inner :: nested) ++ false :: outer } flags ctx
                              = stepChargedKeys (.op .OP_ELSE)
                                  { state with conditions := (inner :: nested) ++ false :: outer } flags ctx +
                                  runKeys oracle rest
                                    { state with
                                      operationCount := count
                                      conditions := (!inner) :: (nested ++ false :: outer) } flags ctx :=
                                runKeys_cons stepped
                            _ = runKeys oracle selected
                                  { state with conditions := [] ++ outer } flags ctx := by
                                rw [headZero, Nat.zero_add, ihKeysN, raisedKeysN]
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        have fitsN : state.operationCount +
                            ((ScriptElement.op .OP_ELSE).executedOpCharge + executedOpCount rest) +
                            runKeys oracle (.op .OP_ELSE :: selectedTail)
                              { state with conditions := (inner :: nested) ++ outer } flags ctx ≤
                            maxOpsPerScript := fits
                        have successN : evaluateRuntime oracle (.op .OP_ELSE :: selectedTail)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx =
                            .success stack alt weight := success
                        obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                          runtime_success_cons successN
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        have eocElse : (ScriptElement.op .OP_ELSE).executedOpCharge = 1 := rfl
                        have sckElse : stepChargedKeys (.op .OP_ELSE)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx = 0 :=
                          stepChargedKeys_eq_zero_of_quiet rfl
                        have deltaN : count = state.operationCount + 1 := by
                          have delta := chargeOperations_executed_delta nontap charging
                          rw [eocElse, sckElse] at delta
                          omega
                        have steppedProj : runtimeStep oracle (.op .OP_ELSE)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := (!inner) :: (nested ++ outer) }) :=
                          runtimeStep_of_charge_execute charging
                            (by simp [executeRuntimeElement, ScriptElement.pushSize,
                              maxScriptElementSize, pure, Except.pure]) nextBound
                        have fitsRest : count + executedOpCount rest +
                            runKeys oracle selectedTail
                              { state with
                                operationCount := count
                                conditions := (!inner) :: (nested ++ outer) } flags ctx ≤
                            maxOpsPerScript := by
                          rw [runKeys_cons (rest := selectedTail) steppedProj] at fitsN
                          omega
                        obtain ⟨ihRun, ihKeys⟩ := ih selectedTail
                          { state with operationCount := count } ((!inner) :: nested) outer true
                          (by simpa using tailProjected) tailPushes tailLegal bounded
                          fitsRest (by exact tail)
                        have ihKeysN : runKeys oracle rest
                            { state with
                              operationCount := count
                              conditions := (!inner) :: (nested ++ true :: outer) } flags ctx =
                            runKeys oracle selectedTail
                              { state with
                                operationCount := count
                                conditions := (!inner) :: (nested ++ outer) } flags ctx := ihKeys
                        have chargingWalk := chargeOperations_conditions
                          (state := { state with conditions := inner :: (nested ++ outer) })
                          (inner :: (nested ++ true :: outer)) (by simp [List.all_append]) charging
                        have executedWalk : executeRuntimeElement oracle (.op .OP_ELSE)
                            { state with
                              operationCount := count
                              conditions := inner :: (nested ++ true :: outer) } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := (!inner) :: (nested ++ true :: outer) }) := by
                          simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        refine ⟨?_, ?_⟩
                        · exact runtime_cons_success chargingWalk executedWalk bounded ihRun
                        · have steppedWalk : runtimeStep oracle (.op .OP_ELSE)
                              { state with conditions := (inner :: nested) ++ true :: outer } flags ctx =
                              .ok ({ state with
                                operationCount := count
                                conditions := (!inner) :: (nested ++ true :: outer) }) :=
                            runtimeStep_of_charge_execute chargingWalk executedWalk bounded
                          have sckWalk : stepChargedKeys (.op .OP_ELSE)
                              { state with conditions := (inner :: nested) ++ true :: outer } flags ctx = 0 :=
                            stepChargedKeys_eq_zero_of_quiet rfl
                          calc runKeys oracle (.op .OP_ELSE :: rest)
                                { state with conditions := (inner :: nested) ++ true :: outer } flags ctx
                              = stepChargedKeys (.op .OP_ELSE)
                                  { state with conditions := (inner :: nested) ++ true :: outer } flags ctx +
                                  runKeys oracle rest
                                    { state with
                                      operationCount := count
                                      conditions := (!inner) :: (nested ++ true :: outer) } flags ctx :=
                                runKeys_cons steppedWalk
                            _ = runKeys oracle selectedTail
                                  { state with
                                    operationCount := count
                                    conditions := (!inner) :: (nested ++ outer) } flags ctx := by
                                rw [sckWalk, Nat.zero_add, ihKeysN]
                            _ = stepChargedKeys (.op .OP_ELSE)
                                  { state with conditions := (inner :: nested) ++ outer } flags ctx +
                                  runKeys oracle selectedTail
                                    { state with
                                      operationCount := count
                                      conditions := (!inner) :: (nested ++ outer) } flags ctx := by
                                rw [sckElse, Nat.zero_add]
                            _ = runKeys oracle (.op .OP_ELSE :: selectedTail)
                                  { state with conditions := (inner :: nested) ++ outer } flags ctx :=
                                (runKeys_cons steppedProj).symm
              case OP_ENDIF =>
                cases nested with
                | nil =>
                    have selectedEq : selected = rest := (Option.some.inj projected).symm
                    subst selected
                    have fitsN : state.operationCount +
                        ((ScriptElement.op .OP_ENDIF).executedOpCharge + executedOpCount rest) +
                        runKeys oracle rest { state with conditions := outer } flags ctx ≤
                        maxOpsPerScript := by
                      have fits' := fits
                      simp only [ifNilGen, List.nil_append] at fits'
                      exact fits'
                    have successN : evaluateRuntime oracle rest
                        { state with conditions := outer } flags ctx =
                        .success stack alt weight := by
                      have success' := success
                      simp only [ifNilGen, List.nil_append] at success'
                      exact success'
                    have eocEndif : (ScriptElement.op .OP_ENDIF).executedOpCharge = 1 := rfl
                    have sckEndif : stepChargedKeys (.op .OP_ENDIF)
                        { state with conditions := [] ++ choice :: outer } flags ctx = 0 :=
                      stepChargedKeys_eq_zero_of_quiet rfl
                    have charging : chargeOperations (.op .OP_ENDIF)
                        { state with conditions := [] ++ choice :: outer } flags ctx =
                        .ok ({ state with
                          operationCount := state.operationCount + 1
                          conditions := [] ++ choice :: outer }) := by
                      simpa only [ScriptElement.executedOpCharge, stepChargedKeys_eq_zero_of_quiet (opcode := .OP_ENDIF) rfl, Nat.add_zero] using
                        chargeOperations_executed_ok (element := .op .OP_ENDIF) nontap
                          (state := { state with conditions := [] ++ choice :: outer })
                          (fun _ same => by cases same; exact ⟨0, rfl⟩)
                          (by rw [sckEndif]
                              show state.operationCount + 1 + 0 ≤ maxOpsPerScript
                              omega)
                    have executed : executeRuntimeElement oracle (.op .OP_ENDIF)
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := [] ++ choice :: outer } flags ctx =
                        .ok ({ state with
                          operationCount := state.operationCount + 1
                          conditions := outer }) := by
                      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap successN
                      (count := state.operationCount + 1)
                      (by omega)
                    have raisedRunN : evaluateRuntime oracle rest
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := outer } flags ctx =
                        .success stack alt weight := raisedRun
                    have raisedKeysN : runKeys oracle rest
                        { state with
                          operationCount := state.operationCount + 1
                          conditions := outer } flags ctx =
                        runKeys oracle rest { state with conditions := outer } flags ctx :=
                      raisedKeys
                    refine ⟨?_, ?_⟩
                    · exact runtime_cons_success charging executed bounded raisedRunN
                    · have stepped : runtimeStep oracle (.op .OP_ENDIF)
                          { state with conditions := [] ++ choice :: outer } flags ctx =
                          .ok ({ state with
                            operationCount := state.operationCount + 1
                            conditions := outer }) :=
                        runtimeStep_of_charge_execute charging executed bounded
                      have goalN : runKeys oracle (.op .OP_ENDIF :: rest)
                            { state with conditions := [] ++ choice :: outer } flags ctx =
                            runKeys oracle rest { state with conditions := outer } flags ctx := by
                        calc runKeys oracle (.op .OP_ENDIF :: rest)
                              { state with conditions := [] ++ choice :: outer } flags ctx
                            = stepChargedKeys (.op .OP_ENDIF)
                                { state with conditions := [] ++ choice :: outer } flags ctx +
                                runKeys oracle rest
                                  { state with
                                    operationCount := state.operationCount + 1
                                    conditions := outer } flags ctx :=
                              runKeys_cons stepped
                          _ = runKeys oracle rest
                                { state with
                                  operationCount := state.operationCount + 1
                                  conditions := outer } flags ctx := by
                              rw [sckEndif, Nat.zero_add]
                          _ = runKeys oracle rest { state with conditions := outer } flags ctx :=
                              raisedKeysN
                      simpa only [ifNilGen, List.nil_append] using goalN
                | cons inner nested =>
                    cases choice with
                    | false =>
                        have tailProjected : selectConditionalTail nested.length false rest =
                            some selected := by
                          simpa [selectConditionalTail] using projected
                        have fitsN : state.operationCount +
                            ((ScriptElement.op .OP_ENDIF).executedOpCharge + executedOpCount rest) +
                            runKeys oracle selected { state with conditions := [] ++ outer } flags ctx ≤
                            maxOpsPerScript := fits
                        have successN : evaluateRuntime oracle selected
                            { state with conditions := [] ++ outer } flags ctx =
                            .success stack alt weight := success
                        have eocEndif : (ScriptElement.op .OP_ENDIF).executedOpCharge = 1 := rfl
                        obtain ⟨count, _, countEq, charging⟩ := chargeOperations_inactive_executed
                          (element := .op .OP_ENDIF) nontap
                          (state := { state with conditions := (inner :: nested) ++ false :: outer })
                          (by simp [List.all_append])
                          (by show state.operationCount + 1 ≤ maxOpsPerScript; omega)
                        have countEqN : count = state.operationCount + 1 := by
                          have countEq' := countEq
                          rw [eocEndif] at countEq'
                          exact countEq'
                        have executed : executeRuntimeElement oracle (.op .OP_ENDIF)
                            { state with
                              operationCount := count
                              conditions := (inner :: nested) ++ false :: outer } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := nested ++ false :: outer }) := by
                          simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        obtain ⟨raisedRun, raisedKeys⟩ := evaluateRuntime_raise_executed nontap
                          successN (count := count)
                          (by have sub := executedOpCount_sublist
                                (selectConditionalTail_sublist tailProjected)
                              omega)
                        have raisedRunN : evaluateRuntime oracle selected
                            { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                            .success stack alt weight := raisedRun
                        have raisedKeysN : runKeys oracle selected
                            { state with operationCount := count, conditions := [] ++ outer } flags ctx =
                            runKeys oracle selected { state with conditions := [] ++ outer } flags ctx :=
                          raisedKeys
                        obtain ⟨ihRun, ihKeys⟩ := ih selected { state with operationCount := count }
                          nested outer false tailProjected tailPushes tailLegal bounded
                          (by show count + executedOpCount rest +
                                runKeys oracle selected
                                  { state with
                                    operationCount := count
                                    conditions := [] ++ outer } flags ctx ≤ maxOpsPerScript
                              omega)
                          raisedRunN
                        have ihKeysN : runKeys oracle rest
                            { state with
                              operationCount := count
                              conditions := nested ++ false :: outer } flags ctx =
                            runKeys oracle selected
                              { state with operationCount := count, conditions := [] ++ outer } flags ctx :=
                          ihKeys
                        refine ⟨?_, ?_⟩
                        · exact runtime_cons_success charging executed bounded ihRun
                        · have stepped : runtimeStep oracle (.op .OP_ENDIF)
                              { state with conditions := (inner :: nested) ++ false :: outer } flags ctx =
                              .ok ({ state with
                                operationCount := count
                                conditions := nested ++ false :: outer }) :=
                            runtimeStep_of_charge_execute charging executed bounded
                          have headZero : stepChargedKeys (.op .OP_ENDIF)
                              { state with conditions := (inner :: nested) ++ false :: outer } flags ctx = 0 :=
                            stepChargedKeys_eq_zero_of_quiet rfl
                          calc runKeys oracle (.op .OP_ENDIF :: rest)
                                { state with conditions := (inner :: nested) ++ false :: outer } flags ctx
                              = stepChargedKeys (.op .OP_ENDIF)
                                  { state with conditions := (inner :: nested) ++ false :: outer } flags ctx +
                                  runKeys oracle rest
                                    { state with
                                      operationCount := count
                                      conditions := nested ++ false :: outer } flags ctx :=
                                runKeys_cons stepped
                            _ = runKeys oracle selected
                                  { state with conditions := [] ++ outer } flags ctx := by
                                rw [headZero, Nat.zero_add, ihKeysN, raisedKeysN]
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        have fitsN : state.operationCount +
                            ((ScriptElement.op .OP_ENDIF).executedOpCharge + executedOpCount rest) +
                            runKeys oracle (.op .OP_ENDIF :: selectedTail)
                              { state with conditions := (inner :: nested) ++ outer } flags ctx ≤
                            maxOpsPerScript := fits
                        have successN : evaluateRuntime oracle (.op .OP_ENDIF :: selectedTail)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx =
                            .success stack alt weight := success
                        obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                          runtime_success_cons successN
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        have eocEndif : (ScriptElement.op .OP_ENDIF).executedOpCharge = 1 := rfl
                        have sckEndif : stepChargedKeys (.op .OP_ENDIF)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx = 0 :=
                          stepChargedKeys_eq_zero_of_quiet rfl
                        have deltaN : count = state.operationCount + 1 := by
                          have delta := chargeOperations_executed_delta nontap charging
                          rw [eocEndif, sckEndif] at delta
                          omega
                        have steppedProj : runtimeStep oracle (.op .OP_ENDIF)
                            { state with conditions := (inner :: nested) ++ outer } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := nested ++ outer }) :=
                          runtimeStep_of_charge_execute charging
                            (by simp [executeRuntimeElement, ScriptElement.pushSize,
                              maxScriptElementSize, pure, Except.pure]) nextBound
                        have fitsRest : count + executedOpCount rest +
                            runKeys oracle selectedTail
                              { state with
                                operationCount := count
                                conditions := nested ++ outer } flags ctx ≤
                            maxOpsPerScript := by
                          rw [runKeys_cons (rest := selectedTail) steppedProj] at fitsN
                          omega
                        obtain ⟨ihRun, ihKeys⟩ := ih selectedTail
                          { state with operationCount := count } nested outer true
                          tailProjected tailPushes tailLegal bounded
                          fitsRest (by exact tail)
                        have ihKeysN : runKeys oracle rest
                            { state with
                              operationCount := count
                              conditions := nested ++ true :: outer } flags ctx =
                            runKeys oracle selectedTail
                              { state with
                                operationCount := count
                                conditions := nested ++ outer } flags ctx := ihKeys
                        have chargingWalk := chargeOperations_conditions
                          (state := { state with conditions := inner :: (nested ++ outer) })
                          (inner :: (nested ++ true :: outer)) (by simp [List.all_append]) charging
                        have executedWalk : executeRuntimeElement oracle (.op .OP_ENDIF)
                            { state with
                              operationCount := count
                              conditions := inner :: (nested ++ true :: outer) } flags ctx =
                            .ok ({ state with
                              operationCount := count
                              conditions := nested ++ true :: outer }) := by
                          simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        refine ⟨?_, ?_⟩
                        · exact runtime_cons_success chargingWalk executedWalk bounded ihRun
                        · have steppedWalk : runtimeStep oracle (.op .OP_ENDIF)
                              { state with conditions := (inner :: nested) ++ true :: outer } flags ctx =
                              .ok ({ state with
                                operationCount := count
                                conditions := nested ++ true :: outer }) :=
                            runtimeStep_of_charge_execute chargingWalk executedWalk bounded
                          have sckWalk : stepChargedKeys (.op .OP_ENDIF)
                              { state with conditions := (inner :: nested) ++ true :: outer } flags ctx = 0 :=
                            stepChargedKeys_eq_zero_of_quiet rfl
                          calc runKeys oracle (.op .OP_ENDIF :: rest)
                                { state with conditions := (inner :: nested) ++ true :: outer } flags ctx
                              = stepChargedKeys (.op .OP_ENDIF)
                                  { state with conditions := (inner :: nested) ++ true :: outer } flags ctx +
                                  runKeys oracle rest
                                    { state with
                                      operationCount := count
                                      conditions := nested ++ true :: outer } flags ctx :=
                                runKeys_cons steppedWalk
                            _ = runKeys oracle selectedTail
                                  { state with
                                    operationCount := count
                                    conditions := nested ++ outer } flags ctx := by
                                rw [sckWalk, Nat.zero_add, ihKeysN]
                            _ = stepChargedKeys (.op .OP_ENDIF)
                                  { state with conditions := (inner :: nested) ++ outer } flags ctx +
                                  runKeys oracle selectedTail
                                    { state with
                                      operationCount := count
                                      conditions := nested ++ outer } flags ctx := by
                                rw [sckEndif, Nat.zero_add]
                            _ = runKeys oracle (.op .OP_ENDIF :: selectedTail)
                                  { state with conditions := (inner :: nested) ++ outer } flags ctx :=
                                (runKeys_cons steppedProj).symm
              all_goals contradiction

/-- Runtime completion with executed-path operation accounting: the source
executed-op count plus the observed executed multisignature keys must fit.
The observation drives one runtime walk whose charged keys are exactly the
observed executed multisignature keys. -/
theorem EvalResources.runtime_complete_executed_general
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources)
    (nontap : ctx.sigVersion ≠ .tapscript)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (legal : ∀ element ∈ script, element.isIllegalOpcode = false)
    (peak : resources.peakStackItems ≤ maxStackSize)
    (base : Nat)
    (operations : base + executedOpCount script + resources.executedMultiSigKeys ≤ maxOpsPerScript)
    (weight : Nat) (enough : resources.signatureWeight ≤ weight) :
    ∃ remaining,
      evaluateRuntime oracle script
          { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx =
        .success finalStack finalAlt remaining ∧
      remaining + resources.signatureWeight = weight ∧
      runKeys oracle script
          { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx =
        resources.executedMultiSigKeys := by
  induction observed generalizing base weight with
  | empty stack altStack flags ctx => exact ⟨weight, rfl, by simp, rfl⟩
  | @step element rest stack alt nextStack nextAlt finalStack finalAlt flags ctx tailResources
      head tail ih =>
      simp only [ExecutionResources.prepend_signatureWeight] at enough ⊢
      simp only [ExecutionResources.prepend_executedMultiSigKeys] at operations ⊢
      simp only [ExecutionResources.prepend_peakStackItems] at peak
      rw [executedOpCount_cons] at operations
      obtain ⟨nextWeight, charged, debit⟩ := prepareValidationWeight_exact (weight := weight) head (by omega)
      have tailPeak : tailResources.peakStackItems ≤ maxStackSize := by omega
      have keysEq : stepChargedKeys element
          { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx =
          executedMultiSigKeyCharge element stack flags ctx :=
        (executedMultiSigKeyCharge_eq_stepChargedKeys nontap rfl head).symm
      have headFits : base + element.executedOpCharge +
          stepChargedKeys element
            { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx ≤
          maxOpsPerScript := by omega
      have charging := chargeOperations_executed_ok nontap
        (state := { stack := stack, altStack := alt, weight := weight, operationCount := base })
        (fun opcode same => opcodeKeyCount_of_eval head nontap opcode same)
        headFits
      obtain ⟨remaining, completed, spent, keysTail⟩ := ih nontap
        (fun element member => pushes element (by simp [member]))
        (fun element member => legal element (by simp [member]))
        tailPeak
        (base + element.executedOpCharge +
          stepChargedKeys element
            { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx)
        (by omega)
        nextWeight (by omega)
      have executed : executeRuntimeElement oracle element
          { stack := stack, altStack := alt, weight := weight, operationCount := base + element.executedOpCharge +
              stepChargedKeys element
                { stack := stack, altStack := alt, weight := weight, operationCount := base }
                flags ctx } flags ctx =
          .ok ({ stack := nextStack, altStack := nextAlt, weight := nextWeight
                 operationCount := base + element.executedOpCharge +
                  stepChargedKeys element
                    { stack := stack, altStack := alt, weight := weight, operationCount := base }
                    flags ctx }) := by
        rw [execute_ordinary element head.singleton_nonConditional head.singleton_legal]
        simp [Nat.not_lt.mpr (pushes element (by simp)), charged,
          evaluate_underTimelockFlags_success (evaluate_eq_of_eval agreement head), bind,
          Except.bind, pure, Except.pure]
      have bounded : nextStack.length + nextAlt.length ≤ maxStackSize :=
        Nat.le_trans tail.initial_le_peak tailPeak
      refine ⟨remaining, ?_, by omega, ?_⟩
      · exact runtime_cons_success charging executed bounded completed
      · have stepped : runtimeStep oracle element
            { stack := stack, altStack := alt, weight := weight, operationCount := base } flags ctx =
            .ok ({ stack := nextStack, altStack := nextAlt, weight := nextWeight
                   operationCount := base + element.executedOpCharge +
                    stepChargedKeys element
                      { stack := stack, altStack := alt, weight := weight, operationCount := base }
                      flags ctx }) :=
          runtimeStep_of_charge_execute charging executed bounded
        rw [runKeys_cons stepped, keysTail, keysEq]
  | @if_execute top rest altStack script frame flags ctx finalStack finalAlt selectedResources
      split minimal selected ih =>
      simp only [ExecutionResources.prepend_signatureWeight] at enough ⊢
      simp only [ExecutionResources.prepend_executedMultiSigKeys] at operations ⊢
      simp only [ExecutionResources.prepend_peakStackItems] at peak
      simp only [executedOpCount_cons, ScriptElement.executedOpCharge] at operations
      have projected : selectConditionalTail 0 (castToBool top) script =
          some (frame.select (castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have selectedPeak : selectedResources.peakStackItems ≤ maxStackSize := by omega
      obtain ⟨remaining, completed, spent, keysTail⟩ := ih nontap
        (fun element member => pushes element (by simp [sub.subset member]))
        (fun element member => legal element (by simp [sub.subset member]))
        selectedPeak (base + 1)
        (by have subLe := executedOpCount_sublist sub; omega)
        weight (by simpa using enough)
      have sckIf : stepChargedKeys (.op .OP_IF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
          flags ctx = 0 :=
        stepChargedKeys_eq_zero_of_quiet rfl
      have charging : chargeOperations (.op .OP_IF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
          flags ctx =
          .ok ({ stack := top :: rest, altStack := altStack, weight := weight, operationCount := base + 1 }) := by
        simpa only [ScriptElement.executedOpCharge, stepChargedKeys_eq_zero_of_quiet (opcode := .OP_IF) rfl, Nat.add_zero] using
          chargeOperations_executed_ok (element := .op .OP_IF) nontap
            (state := { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base })
            (fun _ same => by cases same; exact ⟨0, rfl⟩)
            (by rw [sckIf]; show base + 1 + 0 ≤ maxOpsPerScript; omega)
      have executed : executeRuntimeElement oracle (.op .OP_IF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base + 1 } flags ctx =
          .ok ({ stack := rest, altStack := altStack, conditions := [castToBool top],
                 weight := weight, operationCount := base + 1 }) := by
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, minimal,
          ScriptElement.branchChoice, pure, Except.pure]
      have bounded : rest.length + altStack.length ≤ maxStackSize :=
        Nat.le_trans selected.initial_le_peak selectedPeak
      have ifNil : (if castToBool top then ([] : List Bool) else []) = [] := by
        split <;> rfl
      have fitsRestore : base + 1 + executedOpCount script +
          runKeys oracle (frame.select (castToBool top))
            { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
            flags ctx ≤ maxOpsPerScript := by
        rw [keysTail]; omega
      obtain ⟨restored, keysRestore⟩ := runtime_restore_conditional_executed script
        (frame.select (castToBool top))
        { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
        [] [] (castToBool top) nontap projected
        (fun element member => pushes element (by simp [member]))
        (fun element member => legal element (by simp [member]))
        bounded
        (by rw [ifNil, List.append_nil]; exact fitsRestore)
        (by rw [ifNil, List.append_nil]; exact completed)
      refine ⟨remaining, ?_, by simpa using spent, ?_⟩
      · exact runtime_cons_success charging executed bounded restored
      · have stepped : runtimeStep oracle (.op .OP_IF)
            { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
            flags ctx =
            .ok ({ stack := rest, altStack := altStack, conditions := [castToBool top],
                   weight := weight, operationCount := base + 1 }) :=
          runtimeStep_of_charge_execute charging executed bounded
        have keysRestoreN : runKeys oracle script
            { stack := rest, altStack := altStack, conditions := [castToBool top],
              weight := weight, operationCount := base + 1 } flags ctx =
            runKeys oracle (frame.select (castToBool top))
              { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
              flags ctx := by
          simp only [List.nil_append, ifNil, List.append_nil] at keysRestore
          exact keysRestore
        calc runKeys oracle (.op .OP_IF :: script)
              { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
              flags ctx
            = stepChargedKeys (.op .OP_IF)
                { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
                flags ctx +
                runKeys oracle script
                  { stack := rest, altStack := altStack, conditions := [castToBool top],
                    weight := weight, operationCount := base + 1 } flags ctx :=
              runKeys_cons stepped
          _ = 0 + selectedResources.executedMultiSigKeys := by
              rw [sckIf, keysRestoreN, keysTail]
  | @notif_execute top rest altStack script frame flags ctx finalStack finalAlt selectedResources
      split minimal selected ih =>
      simp only [ExecutionResources.prepend_signatureWeight] at enough ⊢
      simp only [ExecutionResources.prepend_executedMultiSigKeys] at operations ⊢
      simp only [ExecutionResources.prepend_peakStackItems] at peak
      simp only [executedOpCount_cons, ScriptElement.executedOpCharge] at operations
      have projected : selectConditionalTail 0 (!castToBool top) script =
          some (frame.select (!castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have selectedPeak : selectedResources.peakStackItems ≤ maxStackSize := by omega
      obtain ⟨remaining, completed, spent, keysTail⟩ := ih nontap
        (fun element member => pushes element (by simp [sub.subset member]))
        (fun element member => legal element (by simp [sub.subset member]))
        selectedPeak (base + 1)
        (by have subLe := executedOpCount_sublist sub; omega)
        weight (by simpa using enough)
      have sckNotIf : stepChargedKeys (.op .OP_NOTIF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
          flags ctx = 0 :=
        stepChargedKeys_eq_zero_of_quiet rfl
      have charging : chargeOperations (.op .OP_NOTIF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
          flags ctx =
          .ok ({ stack := top :: rest, altStack := altStack, weight := weight, operationCount := base + 1 }) := by
        simpa only [ScriptElement.executedOpCharge, stepChargedKeys_eq_zero_of_quiet (opcode := .OP_NOTIF) rfl, Nat.add_zero] using
          chargeOperations_executed_ok (element := .op .OP_NOTIF) nontap
            (state := { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base })
            (fun _ same => by cases same; exact ⟨0, rfl⟩)
            (by rw [sckNotIf]; show base + 1 + 0 ≤ maxOpsPerScript; omega)
      have executed : executeRuntimeElement oracle (.op .OP_NOTIF)
          { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base + 1 } flags ctx =
          .ok ({ stack := rest, altStack := altStack, conditions := [!castToBool top],
                 weight := weight, operationCount := base + 1 }) := by
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, minimal,
          ScriptElement.branchChoice, pure, Except.pure]
      have bounded : rest.length + altStack.length ≤ maxStackSize :=
        Nat.le_trans selected.initial_le_peak selectedPeak
      have ifNil : (if !castToBool top then ([] : List Bool) else []) = [] := by
        split <;> rfl
      have fitsRestore : base + 1 + executedOpCount script +
          runKeys oracle (frame.select (!castToBool top))
            { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
            flags ctx ≤ maxOpsPerScript := by
        rw [keysTail]; omega
      obtain ⟨restored, keysRestore⟩ := runtime_restore_conditional_executed script
        (frame.select (!castToBool top))
        { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
        [] [] (!castToBool top) nontap projected
        (fun element member => pushes element (by simp [member]))
        (fun element member => legal element (by simp [member]))
        bounded
        (by rw [ifNil, List.append_nil]; exact fitsRestore)
        (by rw [ifNil, List.append_nil]; exact completed)
      refine ⟨remaining, ?_, by simpa using spent, ?_⟩
      · exact runtime_cons_success charging executed bounded restored
      · have stepped : runtimeStep oracle (.op .OP_NOTIF)
            { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
            flags ctx =
            .ok ({ stack := rest, altStack := altStack, conditions := [!castToBool top],
                   weight := weight, operationCount := base + 1 }) :=
          runtimeStep_of_charge_execute charging executed bounded
        have keysRestoreN : runKeys oracle script
            { stack := rest, altStack := altStack, conditions := [!castToBool top],
              weight := weight, operationCount := base + 1 } flags ctx =
            runKeys oracle (frame.select (!castToBool top))
              { stack := rest, altStack := altStack, weight := weight, operationCount := base + 1 }
              flags ctx := by
          simp only [List.nil_append, ifNil, List.append_nil] at keysRestore
          exact keysRestore
        calc runKeys oracle (.op .OP_NOTIF :: script)
              { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
              flags ctx
            = stepChargedKeys (.op .OP_NOTIF)
                { stack := top :: rest, altStack := altStack, weight := weight, operationCount := base }
                flags ctx +
                runKeys oracle script
                  { stack := rest, altStack := altStack, conditions := [!castToBool top],
                    weight := weight, operationCount := base + 1 } flags ctx :=
              runKeys_cons stepped
          _ = 0 + selectedResources.executedMultiSigKeys := by
              rw [sckNotIf, keysRestoreN, keysTail]

/-- Runtime completion with the executed-path operation count observed on the
active path. Outside Tapscript the runtime charges one operation per visited
opcode plus the decoded key count of each active multisignature, so the source
executed-op count plus the observed executed keys suffices. The final weight
plus the observed debit equals the initial budget. -/
theorem EvalResources.runtime_complete_executed
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources)
    (nontap : ctx.sigVersion ≠ .tapscript)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (legal : ∀ element ∈ script, element.isIllegalOpcode = false)
    (peak : resources.peakStackItems ≤ maxStackSize)
    (operations : executedOpCount script + resources.executedMultiSigKeys ≤ maxOpsPerScript)
    (weight : Nat) (enough : resources.signatureWeight ≤ weight) :
    ∃ remaining,
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
        .success finalStack finalAlt remaining ∧
      remaining + resources.signatureWeight = weight := by
  obtain ⟨remaining, completed, spent, _⟩ := observed.runtime_complete_executed_general agreement
    nontap pushes legal peak 0 (by omega) weight enough
  exact ⟨remaining, completed, spent⟩

end LeanMiniscript.Script
