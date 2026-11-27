import LeanMiniscript.Extraction.TapscriptFrameRecovery
import LeanMiniscript.Extraction.TapscriptThresholdFrames

/-! Normalize true outputs of arbitrary bounded executions of unit-typed B and W fragments. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

variable {sc : ScriptContext}

def UnitBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (env : SatEnv) (flags : ScriptFlags) (input rest : Stack) (top : StackElement),
    ModeledContextVersion sc env.txCtx →
    (∀ item ∈ input, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) input [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = true → top = trueElement

def UnitWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (env : SatEnv) (flags : ScriptFlags) (own : Witness) (saved top : StackElement)
    (rest : Stack) (order : BaseWOutputOrder),
    ModeledContextVersion sc env.txCtx →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = true → top = trueElement

abbrev UnitB := UnitBIn .tapscript
abbrev UnitW := UnitWIn .tapscript

private theorem minimal_selector {flags : ScriptFlags} {ctx : TxContext} {selector : StackElement}
    (version : ctx.sigVersion = .tapscript)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector) :
    selector = falseElement ∨ selector = trueElement := by
  have eqs : selector.data = falseElement.data ∨ selector.data = trueElement.data := by
    simpa [minimalIfSatisfied, version, minimalIfArg, stackElementEq, Bool.or_eq_true] using minimal
  rcases eqs with h | h
  · exact Or.inl (congrArg ByteArray.mk h)
  · exact Or.inr (congrArg ByteArray.mk h)

private def shortCircuit (keep : Bool) (X Y : CoreFragment) : CoreFragment :=
  if keep then .or_d X Y else .or_c X Y

private def shortCircuitTail (keep : Bool) (body : Script) : Script :=
  (if keep then [.op .OP_IFDUP] else []) ++ [.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF]

private theorem shortCircuit_tail_cases {keep : Bool} {body : Script} {selector : StackElement}
    {rest alt out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval (shortCircuitTail keep body) (selector :: rest) alt flags ctx (.success out outAlt)) :
    (castToBool selector = true ∧ out = (if keep then selector :: rest else rest) ∧ outAlt = alt) ∨
    (castToBool selector = false ∧ Eval body rest alt flags ctx (.success out outAlt)) := by
  cases keep with
  | false => exact LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced run
  | true =>
    have combined : Eval ([.op .OP_IFDUP] ++ ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF]))
        (selector :: rest) alt flags ctx (.success out outAlt) := by
      simpa [shortCircuitTail, List.append_assoc] using run
    obtain ⟨mid, midAlt, dupRun, conditionalRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
        (.atom (by simp [NonConditional])) combined
    cases truth : castToBool selector with
    | false =>
      have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest) alt flags ctx
          (.success (selector :: rest) alt) :=
        Eval.ifdup_false selector rest alt [] flags ctx _ truth Eval.done
      have eq := Eval.result_unique dupRun canonicalDup
      cases eq
      rcases LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced conditionalRun with
          ⟨h, _, _⟩ | ⟨_, childRun⟩
      · simp [truth] at h
      · exact Or.inr ⟨rfl, childRun⟩
    | true =>
      have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest) alt flags ctx
          (.success (selector :: selector :: rest) alt) :=
        Eval.ifdup_true selector rest alt [] flags ctx _ truth Eval.done
      have eq := Eval.result_unique dupRun canonicalDup
      cases eq
      rcases LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced conditionalRun with
          ⟨_, outEq, altEq⟩ | ⟨h, _⟩
      · exact Or.inl ⟨rfl, outEq, altEq⟩
      · simp [truth] at h

private theorem shortCircuit_run_cases {X Y : CoreFragment} {modsX : CorrectnessModifiers}
    {keep : Bool} {env : SatEnv} {flags : ScriptFlags} {input out : Stack}
    (typedX : HasType sc X ⟨.B, modsX⟩) (wfX : X.WellFormed sc)
    (run : Eval (compile (shortCircuit keep X Y)) input [] flags env.txCtx (.success out [])) :
    (∃ args rest top, input = args ++ rest ∧
      Eval (compile X) (args ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = true ∧ out = (if keep then top :: rest else rest)) ∨
    (∃ args rest top, input = args ++ rest ∧
      Eval (compile X) (args ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = false ∧ Eval (compile Y) rest [] flags env.txCtx (.success out [])) := by
  have combined : Eval (compile X ++ shortCircuitTail keep (compile Y)) input [] flags env.txCtx
      (.success out []) := by
    cases keep <;> simpa [shortCircuit, shortCircuitTail, compile, compileWithKeyHash,
      List.append_assoc] using run
  obtain ⟨mid, midAlt, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX input [] flags env.txCtx
    (.success mid midAlt) runX
  cases altEq
  obtain ⟨args, rest, top, inputEq, outputEq, _⟩ := effect.b_inv
  rw [outputEq] at tailRun runX
  rw [inputEq] at runX
  rcases shortCircuit_tail_cases (compile_balancedControlFlow Y) tailRun with
      ⟨truth, outEq, _⟩ | ⟨falsehood, runY⟩
  · exact Or.inl ⟨args, rest, top, inputEq, runX, truth, outEq⟩
  · exact Or.inr ⟨args, rest, top, inputEq, runX, falsehood, runY⟩

private theorem d_success_child {X : CoreFragment} {input rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.d X)) input [] flags ctx (.success (top :: rest) []))
    (truth : castToBool top = true) : Eval (compile X) input [] flags ctx (.success (top :: rest) []) := by
  have combined : Eval ([.op .OP_DUP] ++ ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF]))
      input [] flags ctx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, midAlt, dupRun, conditionalRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (.atom (by simp [NonConditional])) combined
  cases input with
  | nil =>
    have failed := Eval.fixedArityStackUnderflow_result
      (opcode := .OP_DUP) (required := 1) (arity := rfl) (underflow := by simp) dupRun
    contradiction
  | cons selector tail =>
    have canonical : Eval [.op .OP_DUP] (selector :: tail) [] flags ctx
        (.success (selector :: selector :: tail) []) :=
      Eval.dup selector tail [] [] flags ctx _ Eval.done
    have eq := Eval.result_unique dupRun canonical
    cases eq
    rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditionalRun with
        ⟨falsehood, outEq, _altEq⟩ | ⟨_selected, childRun⟩
    · have topEq := (List.cons.inj outEq).1
      rw [topEq, falsehood] at truth
      cases truth
    · exact childRun

private theorem j_success_child {X : CoreFragment} {input rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.j X)) input [] flags ctx (.success (top :: rest) []))
    (truth : castToBool top = true) : Eval (compile X) input [] flags ctx (.success (top :: rest) []) := by
  change Eval ([.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
    input [] flags ctx (.success (top :: rest) []) at run
  cases run with
  | size operand tail alt script flags ctx result inner =>
    cases inner with
    | zeroNotEqual sizeBytes value tail' alt' script' flags' ctx' result' decoded conditionalRun =>
      have canonical := decodeScriptNum_scriptNat_of_le_maxScriptElementSize (bounded operand (by simp)) flags.minimalData
      rw [canonical] at decoded
      cases decoded
      have conditional : Eval ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
          (boolToElement ((operand.size : Int) != 0) :: operand :: tail) [] flags ctx (.success (top :: rest) []) := by
        simpa [List.append_assoc] using conditionalRun
      rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditional with
          ⟨falsehood, outEq, _altEq⟩ | ⟨_selected, childRun⟩
      · have sizeZero : operand.size = 0 := by simpa using falsehood
        have empty := ByteArray.size_eq_zero_iff.mp sizeZero
        have topEq := (List.cons.inj outEq).1
        rw [topEq, empty] at truth
        change false = true at truth
        cases truth
      · exact childRun
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

private inductive UnitOpcode : Opcode → Prop where
  | checksig : UnitOpcode .OP_CHECKSIG
  | equal : UnitOpcode .OP_EQUAL
  | numequal : UnitOpcode .OP_NUMEQUAL
  | booland : UnitOpcode .OP_BOOLAND
  | boolor : UnitOpcode .OP_BOOLOR
  | zeroNotEqual : UnitOpcode .OP_0NOTEQUAL

private theorem unit_opcode {opcode : Opcode} (unit : UnitOpcode opcode)
    {input rest alt outAlt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op opcode] input alt flags ctx (.success (top :: rest) outAlt))
    (truth : castToBool top = true) : top = trueElement := by
  cases unit <;> cases run <;> try { simp_all [Opcode.isUpgradeableNop]; done }
  all_goals rename_i next
  all_goals cases next
  all_goals simp_all [boolToElement]
  all_goals split at truth <;> simp_all
  all_goals grind

private theorem unit_last {fragment : CoreFragment} {body : Script} {opcode : Opcode}
    (shape : compile fragment = body ++ [.op opcode])
    (balanced : BalancedControlFlow body) (unit : UnitOpcode opcode) : UnitBIn sc fragment := by
  intro env flags input rest top _version _bounded run truth
  rw [shape] at run
  obtain ⟨mid, midAlt, _before, last⟩ := LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success balanced run
  exact unit_opcode unit last truth

private theorem unit_and_v {X Y : CoreFragment} {mx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.V, mx⟩) (wx : X.WellFormed sc)
    (uy : UnitBIn sc Y) : UnitBIn sc (.and_v X Y) := by
  intro env flags input rest top version bounded run truth
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, alt, rx, ry⟩ := LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨rfl, effect⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ rx
  obtain ⟨args, eq, _⟩ := effect.v_inv
  apply uy env flags mid rest top version _ ry truth
  intro item member
  apply bounded item
  rw [eq]
  exact List.mem_append_right _ member

private theorem unit_or_i {X Y : CoreFragment} (ux : UnitBIn sc X) (uy : UnitBIn sc Y) : UnitBIn sc (.or_i X Y) := by
  intro env flags input rest top version bounded run truth
  change Eval ([.op .OP_IF] ++ compile X ++ [.op .OP_ELSE] ++ compile Y ++ [.op .OP_ENDIF])
    input [] flags env.txCtx (.success (top :: rest) []) at run
  cases input with
  | nil =>
    have failed := Eval.fixedArityStackUnderflow_result
      (opcode := .OP_IF) (required := 1) (arity := rfl) (underflow := by simp) run
    contradiction
  | cons selector tail =>
    have tailBound := fun item h => bounded item (List.mem_cons_of_mem selector h)
    rcases Miniscript.Eval.ifElse_success_cases (compile_balancedControlFlow X)
      (compile_balancedControlFlow Y) run with rx | ry
    · exact ux env flags tail rest top version tailBound rx truth
    · exact uy env flags tail rest top version tailBound ry truth

private theorem unit_or_d {X Y : CoreFragment} {mx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, mx⟩) (wx : X.WellFormed sc)
    (ux : UnitBIn sc X) (uy : UnitBIn sc Y) : UnitBIn sc (.or_d X Y) := by
  intro env flags input rest top version bounded run truth
  rcases shortCircuit_run_cases (keep := true) tx wx run with
    ⟨args, tail, value, eq, rx, trueX, out⟩ | ⟨args, tail, value, eq, _rx, _falseX, ry⟩
  · simp only [ite_true, List.cons.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    exact ux env flags _ _ _ version (eq ▸ bounded) rx trueX
  · apply uy env flags tail rest top version _ ry truth
    intro item member
    apply bounded item
    rw [eq]
    exact List.mem_append_right _ member

private theorem unit_andor {X Y Z : CoreFragment} {mx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, mx⟩) (wx : X.WellFormed sc)
    (uy : UnitBIn sc Y) (uz : UnitBIn sc Z) : UnitBIn sc (.andor X Y Z) := by
  intro env flags input rest top version bounded run truth
  have combined : Eval (compile X ++ ([.op .OP_NOTIF] ++ compile Z ++ [.op .OP_ELSE] ++ compile Y ++ [.op .OP_ENDIF]))
      input [] flags env.txCtx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, alt, rx, branches⟩ := LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨rfl, effect⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ rx
  obtain ⟨args, tail, value, eq, out, _⟩ := effect.b_inv
  rw [out] at branches
  have bound : ∀ item ∈ tail, item.size ≤ maxScriptElementSize := by
    intro item member
    apply bounded item
    rw [eq]
    exact List.mem_append_right _ member
  rcases Miniscript.Eval.notifElse_success_cases (compile_balancedControlFlow Z) (compile_balancedControlFlow Y) branches with
    rz | ry
  · exact uz env flags tail rest top version bound rz truth
  · exact uy env flags tail rest top version bound ry truth

private theorem unit_j {X : CoreFragment} (ux : UnitBIn sc X) : UnitBIn sc (.j X) := by
  intro env flags input rest top version bounded run truth
  exact ux env flags input rest top version bounded (j_success_child bounded run truth) truth

private theorem if_minimal_of_success {script : Script} {selector : StackElement} {input alt output outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (.op .OP_IF :: script) (selector :: input) alt flags ctx (.success output outAlt)) :
    minimalIfSatisfied flags ctx.sigVersion selector := by
  generalize resultEq : ExecResult.success output outAlt = result at run
  cases run <;> simp_all [Opcode.isUpgradeableNop]

private theorem unit_d {X : CoreFragment} {mx : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.V, mx⟩) (wx : X.WellFormed .tapscript)
    (zero : mx.z = true) : UnitBIn .tapscript (.d X) := by
  intro env flags input rest top version _bounded run truth
  have rx := d_success_child run truth
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ rx
  obtain ⟨args, eq, arity⟩ := effect.v_inv
  have empty : args = [] := List.eq_nil_of_length_eq_zero (arity.1 zero)
  have inputEq : input = top :: rest := by simpa [empty] using eq
  rw [inputEq] at run
  change Eval (.op .OP_DUP :: (.op .OP_IF :: (compile X ++ [.op .OP_ENDIF]))) _ _ _ _ _ at run
  generalize outputEq : ExecResult.success (top :: rest) [] = output at run
  cases run <;> try { simp_all [Opcode.isUpgradeableNop]; done }
  case dup =>
    rename_i next
    cases outputEq
    have minimal := if_minimal_of_success next
    rcases minimal_selector version minimal with falseTop | trueTop
    · rw [falseTop] at truth
      cases truth
    · exact trueTop
  all_goals cases outputEq

/-- Arbitrary bounded successful B execution with u=true is normalized.
The induction follows the executed branch. -/
theorem unitB_of_hasType {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.B, mods⟩) (wf : fragment.WellFormed sc)
    (u : mods.u = true) : UnitBIn sc fragment := by
  generalize typeEq : (⟨.B, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have unitEq : ty.mods.u = true := by rw [← typeEq]; exact u
  cases typed <;> try { cases baseEq }
  case zero =>
    intro env flags input rest top _version _bounded run truth
    have canonical : Eval (compile .zero) input [] flags env.txCtx (.success (falseElement :: input) []) :=
      Eval.pushNum _ _ _ _ _ _ _ Eval.done
    cases Eval.result_unique run canonical
    cases truth
  case one =>
    intro env flags input rest top _version _bounded run _truth
    have canonical : Eval (compile .one) input [] flags env.txCtx (.success (trueElement :: input) []) :=
      Eval.pushNum _ _ _ _ _ _ _ Eval.done
    cases Eval.result_unique run canonical
    rfl
  case older => cases unitEq
  case after => cases unitEq
  case sha256 hash =>
    exact unit_last (body := [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_SHA256, .pushData hash])
      rfl (.ofAllNonConditional (by simp [AllNonConditional, NonConditional])) .equal
  case hash256 hash =>
    exact unit_last (body := [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH256, .pushData hash])
      rfl (.ofAllNonConditional (by simp [AllNonConditional, NonConditional])) .equal
  case ripemd160 hash =>
    exact unit_last (body := [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_RIPEMD160, .pushData hash])
      rfl (.ofAllNonConditional (by simp [AllNonConditional, NonConditional])) .equal
  case hash160 hash =>
    exact unit_last (body := [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH160, .pushData hash])
      rfl (.ofAllNonConditional (by simp [AllNonConditional, NonConditional])) .equal
  case and_v tx ty _branch =>
    rename_i X Y mx tyY
    cases tyY with
    | mk base cm =>
      change BaseType.B = base at baseEq
      subst base
      exact unit_and_v tx wf.1 (unitB_of_hasType ty wf.2.1 unitEq)
  case and_b tx ty =>
    exact unit_last rfl (.append (compile_balancedControlFlow _) (compile_balancedControlFlow _)) .booland
  case or_b tx _dx ty _dy =>
    exact unit_last rfl (.append (compile_balancedControlFlow _) (compile_balancedControlFlow _)) .boolor
  case or_d tx _dx ux ty =>
    exact unit_or_d tx wf.1 (unitB_of_hasType tx wf.1 ux) (unitB_of_hasType ty wf.2 unitEq)
  case or_i tx ty _branch same =>
    rename_i X Y tyX tyY
    cases tyX with
    | mk bx mx =>
      change BaseType.B = bx at baseEq
      subst bx
      cases tyY with
      | mk by_ my =>
        change BaseType.B = by_ at same
        subst by_
        obtain ⟨ux, uy⟩ := Bool.and_eq_true_iff.mp unitEq
        exact unit_or_i (unitB_of_hasType tx wf.1 ux) (unitB_of_hasType ty wf.2 uy)
  case andor tx _dx _ux ty tz _branch same =>
    rename_i X Y Z mx tyY tyZ
    cases tyY with
    | mk by_ my =>
      change BaseType.B = by_ at baseEq
      subst by_
      cases tyZ with
      | mk bz mz =>
        change BaseType.B = bz at same
        subst bz
        obtain ⟨uy, uz⟩ := Bool.and_eq_true_iff.mp unitEq
        exact unit_andor tx wf.1 (unitB_of_hasType ty wf.2.1 uy) (unitB_of_hasType tz wf.2.2.1 uz)
  case c_wrap tx => exact unit_last rfl (compile_balancedControlFlow _) .checksig
  case d_wrap tx zero =>
    cases sc with
    | p2wsh => contradiction
    | tapscript => exact unit_d tx wf zero
  case j_wrap tx _nonzero => exact unit_j (unitB_of_hasType tx wf unitEq)
  case n_wrap tx => exact unit_last rfl (compile_balancedControlFlow _) .zeroNotEqual
  case thresh firstTyped fd fu tailTyped tailShape positive atMost =>
    intro env flags input rest top _version _bounded run truth
    exact (typed_threshold_run_inv (.thresh firstTyped fd fu tailTyped tailShape positive atMost) wf run truth).2.1
  case multi =>
    intro env flags input rest top _ _ run truth
    obtain ⟨_, _, _, _, result, _, output, _⟩ :=
      Miniscript.Eval.legacyMulti_checked_frame wf.2.2.1 wf.2.1.2 run
    obtain ⟨rfl, _⟩ := List.cons.inj output
    cases result <;> first | rfl | cases truth
  case multi_a k keys _positive _atMost =>
    apply unit_last (body := compileCheckSigAdd keys ++ [.pushNum k]) (opcode := .OP_NUMEQUAL)
    · simp [compile, compileWithKeyHash, List.append_assoc]
    · exact .append (compileCheckSigAdd_balancedControlFlow keys) (.atom (by trivial))
    · exact .numequal
termination_by sizeOf fragment

/-- Both W wrappers inherit normalization from their B child, using the
already checked alternate-stack transfer for a:. -/
theorem unitW_of_hasType {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.W, mods⟩) (wf : fragment.WellFormed sc)
    (u : mods.u = true) : UnitWIn sc fragment := by
  generalize typeEq : (⟨.W, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have unitEq : ty.mods.u = true := by rw [← typeEq]; exact u
  cases typed <;> try { cases baseEq }
  case and_v tx ty branch =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case or_i tx ty branch same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case andor tx d u ty tz branch same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case a_wrap tx =>
    intro env flags own saved top rest order version bounded run truth
    have childRun := a_run_child tx wf run
    have transferred := Miniscript.Eval.compile_erase_altStack childRun
    exact unitB_of_hasType tx wf unitEq env flags _ rest top version
      (fun item h => bounded item (List.mem_cons_of_mem _ h)) transferred truth
  case s_wrap tx one =>
    intro env flags own saved top rest order version bounded run truth
    obtain ⟨_one, childRun⟩ := s_run_child tx one wf run
    apply unitB_of_hasType tx wf unitEq env flags _ (saved :: rest) top version _ childRun truth
    intro item member
    apply bounded item
    simp only [List.mem_cons, List.mem_append] at member ⊢
    rcases member with member | rfl | member
    · exact Or.inr (Or.inl member)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr member)

end LeanMiniscript.Extraction.TapscriptWitness
