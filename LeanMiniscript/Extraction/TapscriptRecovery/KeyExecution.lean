import LeanMiniscript.Extraction.TapscriptRecovery.BooleanExecution

/-! Track the signature argument through compound K fragments and W boolean operators. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.CompoundK

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames OrI SignedV BExecution BWrappers

theorem typed_K_input_frame {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {input rest : Stack} {top : StackElement}
    (typed : HasType .tapscript fragment ⟨.K, mods⟩) (wf : fragment.WellFormed .tapscript)
    (run : Eval (compile fragment) input [] flags env.txCtx (.success (top :: rest) [])) :
    ∃ consumed : Witness, input = consumed.toInitialStack ++ rest := by
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf
    input [] flags env.txCtx (.success (top :: rest) []) run
  obtain ⟨args, tail, value, eq, outEq, _⟩ := effect.k_inv
  injection outEq with _ tailEq
  subst tail
  exact ⟨args.reverse, by simpa [Witness.toInitialStack] using eq⟩

theorem or_i_run_K {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType .tapscript X ⟨.K, modsX⟩) (typedY : HasType .tapscript Y ⟨.K, modsY⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (version : env.txCtx.sigVersion = .tapscript)
    (run : Eval (compile (.or_i X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    (∃ consumed, other = consumed ++ [trueElement] ∧
      Eval (compile X) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) [])) ∨
    (∃ consumed, other = consumed ++ [falseElement] ∧
      Eval (compile Y) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) [])) := by
  rcases or_i_run_cases version run with ⟨stack, eq, childRun⟩ | ⟨stack, eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_K_input_frame typedX wfX childRun
    exact Or.inl ⟨consumed, witness_selector_frame eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_K_input_frame typedY wfY childRun
    exact Or.inr ⟨consumed, witness_selector_frame eq, childRun⟩

theorem and_v_run_K_frame {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType .tapscript X ⟨.V, modsX⟩) (typedY : HasType .tapscript Y ⟨.K, modsY⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (run : Eval (compile (.and_v X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    ∃ otherX otherY, other = otherY ++ otherX ∧
      Eval (compile X) (otherX.toInitialStack ++ (otherY.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (otherY.toInitialStack ++ rest) []) ∧
      Eval (compile Y) (otherY.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, runY⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  obtain ⟨argsX, inputEqX, _⟩ := effectX.v_inv
  cases altEqX
  obtain ⟨otherY, inputEqY⟩ := typed_K_input_frame typedY wfY runY
  have inputEq : other.toInitialStack = argsX ++ otherY.toInitialStack := by
    apply List.append_cancel_right
    simpa [inputEqY, List.append_assoc] using inputEqX
  have otherEq : other = otherY ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, otherY, otherEq, ?_, ?_⟩
  · rw [inputEqX, inputEqY] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← inputEqY]; exact runY

theorem branch_K_frame {X Y : CoreFragment} {modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest args tail : Stack} {top resultTop : StackElement}
    (typedY : HasType .tapscript Y ⟨.K, modsY⟩) (wfY : Y.WellFormed .tapscript)
    (inputEq : other.toInitialStack ++ rest = args ++ tail)
    (runX : Eval (compile X) (args ++ tail) [] flags env.txCtx (.success (top :: tail) []))
    (runY : Eval (compile Y) tail [] flags env.txCtx (.success (resultTop :: rest) [])) :
    ∃ left right, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) []) := by
  obtain ⟨right, tailEq⟩ := typed_K_input_frame typedY wfY runY
  have stackEq : other.toInitialStack = args ++ right.toInitialStack := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputEq
  have otherEq : other = right ++ args.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  refine ⟨args.reverse, right, otherEq, ?_, ?_⟩
  · rw [tailEq] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← tailEq]; exact runY

theorem andor_run_K_frame {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {resultTop : StackElement}
    (typedX : HasType .tapscript X ⟨.B, modsX⟩)
    (typedY : HasType .tapscript Y ⟨.K, modsY⟩) (typedZ : HasType .tapscript Z ⟨.K, modsZ⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript) (wfZ : Z.WellFormed .tapscript)
    (run : Eval (compile (.andor X Y Z)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) [])) :
    (∃ left right top, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧ castToBool top = false ∧
      Eval (compile Z) (right.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) [])) ∨
    (∃ left right top, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧ castToBool top = true ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) [])) := by
  have combined : Eval (compile X ++ ([.op .OP_NOTIF] ++ compile Z ++ [.op .OP_ELSE] ++ compile Y ++ [.op .OP_ENDIF]))
      (other.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, midAlt, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  cases altEq
  obtain ⟨args, tail, top, inputEq, outputEq, _⟩ := effect.b_inv
  rw [outputEq] at tailRun runX
  rw [inputEq] at runX
  rcases notifElse_truth_cases (compile_balancedControlFlow Z) (compile_balancedControlFlow Y) tailRun with
      ⟨falsehood, runZ⟩ | ⟨truth, runY⟩
  · obtain ⟨left, right, eq, rx, rz⟩ := branch_K_frame typedZ wfZ inputEq runX runZ
    exact Or.inl ⟨left, right, top, eq, rx, falsehood, rz⟩
  · obtain ⟨left, right, eq, rx, ry⟩ := branch_K_frame typedY wfY inputEq runX runY
    exact Or.inr ⟨left, right, top, eq, rx, truth, ry⟩

def AmbientKeyOutput (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (keyBytes : StackElement) (rest : Stack),
    ExecutionContext parent fragment env flags parentArgs parentOther consumed →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (keyBytes :: rest) []) →
    ∃ key ∈ fragment.keys, keyBytes = key.bytes

theorem keyOutput_pk_k (key : PubKey) : AmbientKeyOutput (.pk_k key) := by
  intro parent env flags pa po consumed keyBytes rest _context run
  have canonical : Eval (compile (.pk_k key)) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (key.bytes :: (consumed.toInitialStack ++ rest)) []) := Eval.pushDataNext Eval.done
  have eq := Eval.result_unique run canonical
  exact ⟨key, by simp [CoreFragment.keys], (List.cons.inj (ExecResult.success.inj eq).1).1⟩

theorem pk_h_run_key {key : PubKey} {input rest : Stack} {keyBytes : StackElement}
    {env : SatEnv} {flags : ScriptFlags}
    (run : Eval (compile (.pk_h key)) input [] flags env.txCtx (.success (keyBytes :: rest) [])) :
    input = keyBytes :: rest ∧ LeanMiniscript.Script.hash160 keyBytes = LeanMiniscript.Script.hash160 key.bytes := by
  change Eval [.op .OP_DUP, .op .OP_HASH160, .pushData (LeanMiniscript.Script.hash160 key.bytes),
    .op .OP_EQUALVERIFY] input [] flags env.txCtx (.success (keyBytes :: rest) []) at run
  cases run with
  | dup x tail script alt flags ctx result inner =>
    cases inner with
    | op_hash160 x' tail' script' alt' flags' ctx' result' inner =>
      cases inner with
      | pushData data tail'' init alt'' flags'' ctx'' result'' inner =>
        cases inner with
        | equalverify_success a b tail''' script''' alt''' flags''' ctx''' result''' imageEq final =>
          cases final with
          | empty stack alt flags ctx => exact ⟨rfl, imageEq.symm⟩
        | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem keyOutput_pk_h (key : PubKey) : AmbientKeyOutput (.pk_h key) := by
  intro parent env flags pa po consumed keyBytes rest context run
  obtain ⟨inputEq, imageEq⟩ := pk_h_run_key run
  have ownEq : consumed = [keyBytes] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right inputEq)
  have bytesEq := context.thirdParty.2.2.2 keyBytes (context.consumedIn keyBytes (by simp [ownEq]))
    key (context.childKeys key (by simp [CoreFragment.keys])) imageEq
  exact ⟨key, by simp [CoreFragment.keys], bytesEq⟩

theorem keyOutput_and_v {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType .tapscript X ⟨.V, modsX⟩) (typedY : HasType .tapscript Y ⟨.K, modsY⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (outputY : AmbientKeyOutput Y) : AmbientKeyOutput (.and_v X Y) := by
  intro parent env flags pa po consumed keyBytes rest context run
  obtain ⟨left, right, eq, _runX, runY⟩ := and_v_run_K_frame typedX typedY wfX wfY run
  subst consumed
  have contextY := executionContext_restrict context (active := Y)
    (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
    (fun _ h => List.mem_append_left _ h)
  obtain ⟨key, hk, eq⟩ := outputY parent env flags pa po right keyBytes rest contextY runY
  exact ⟨key, List.mem_append_right _ hk, eq⟩

theorem keyOutput_or_i {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType .tapscript X ⟨.K, modsX⟩) (typedY : HasType .tapscript Y ⟨.K, modsY⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (outputX : AmbientKeyOutput X) (outputY : AmbientKeyOutput Y) : AmbientKeyOutput (.or_i X Y) := by
  intro parent env flags pa po consumed keyBytes rest context run
  rcases or_i_run_K typedX typedY wfX wfY context.version run with ⟨active, eq, runX⟩ | ⟨active, eq, runY⟩
  · subst consumed
    have contextX := executionContext_restrict context (active := X)
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ h)
    obtain ⟨key, hk, eq⟩ := outputX parent env flags pa po active keyBytes rest contextX runX
    exact ⟨key, List.mem_append_left _ hk, eq⟩
  · subst consumed
    have contextY := executionContext_restrict context (active := Y)
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
      (fun _ h => List.mem_append_left _ h)
    obtain ⟨key, hk, eq⟩ := outputY parent env flags pa po active keyBytes rest contextY runY
    exact ⟨key, List.mem_append_right _ hk, eq⟩

theorem keyOutput_andor {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    (typedX : HasType .tapscript X ⟨.B, modsX⟩)
    (typedY : HasType .tapscript Y ⟨.K, modsY⟩) (typedZ : HasType .tapscript Z ⟨.K, modsZ⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript) (wfZ : Z.WellFormed .tapscript)
    (outputY : AmbientKeyOutput Y) (outputZ : AmbientKeyOutput Z) : AmbientKeyOutput (.andor X Y Z) := by
  intro parent env flags pa po consumed keyBytes rest context run
  rcases andor_run_K_frame typedX typedY typedZ wfX wfY wfZ run with
      ⟨left, right, top, eq, _runX, _falsehood, runZ⟩ | ⟨left, right, top, eq, _runX, _truth, runY⟩
  · subst consumed
    have contextZ := executionContext_restrict context (active := Z)
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
      (fun _ h => List.mem_append_left _ h)
    obtain ⟨key, hk, eq⟩ := outputZ parent env flags pa po right keyBytes rest contextZ runZ
    exact ⟨key, List.mem_append_right _ hk, eq⟩
  · subst consumed
    have contextY := executionContext_restrict context (active := Y)
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h))
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h))
      (fun _ h => List.mem_append_left _ h)
    obtain ⟨key, hk, eq⟩ := outputY parent env flags pa po right keyBytes rest contextY runY
    exact ⟨key, List.mem_append_left _ (List.mem_append_right _ hk), eq⟩

theorem keyOutput_of_typed {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript fragment ⟨.K, mods⟩) (wf : fragment.WellFormed .tapscript) :
    AmbientKeyOutput fragment := by
  cases typed_K_shape typed with
  | pk_k key => exact keyOutput_pk_k key
  | pk_h key => exact keyOutput_pk_h key
  | and_v typedX typedY =>
    exact keyOutput_and_v typedX typedY wf.1 wf.2.1 (keyOutput_of_typed typedY wf.2.1)
  | or_i typedX typedY =>
    exact keyOutput_or_i typedX typedY wf.1 wf.2
      (keyOutput_of_typed typedX wf.1) (keyOutput_of_typed typedY wf.2)
  | andor typedX _d _u typedY typedZ =>
    exact keyOutput_andor typedX typedY typedZ wf.1 wf.2.1 wf.2.2.1
      (keyOutput_of_typed typedY wf.2.1) (keyOutput_of_typed typedZ wf.2.2.1)
termination_by sizeOf fragment

theorem checksig_truth_frame {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIG] input alt flags ctx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ keyBytes sig, input = keyBytes :: sig :: rest ∧ alt = [] ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig keyBytes = .ok true := by
  cases run with
  | checksig_success keyBytes sig tail script alt flags ctx result checked final =>
    cases final with
    | empty stack alt flags ctx => exact ⟨keyBytes, sig, rfl, rfl, checked⟩
  | checksig_failure keyBytes sig tail script alt flags ctx result _checked final =>
    cases final with
    | empty stack alt flags ctx => simp [castToBool, falseElement] at truth
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem c_run_frame {X : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript X ⟨.K, mods⟩) (wf : X.WellFormed .tapscript)
    (run : Eval (compile (.c X)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ (own : Witness) (sig keyBytes : StackElement), other = [sig] ++ own ∧
      Eval (compile X) (own.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
        (.success (keyBytes :: sig :: rest) []) ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig keyBytes = .ok true := by
  change Eval (compile X ++ [.op .OP_CHECKSIG]) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, checkRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨keyBytes, sig, midEq, altEq, checked⟩ := checksig_truth_frame checkRun truth
  subst midAlt
  rw [midEq] at runX
  obtain ⟨own, inputEq⟩ := typed_K_input_frame typed wf runX
  have stackEq : other.toInitialStack = own.toInitialStack ++ [sig] := by
    apply List.append_cancel_right
    simpa [List.append_assoc] using inputEq
  have otherEq : other = [sig] ++ own := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  exact ⟨own, sig, keyBytes, otherEq, by rw [← inputEq]; exact runX, checked⟩

theorem c_success_checked {X : CoreFragment} {mods : CorrectnessModifiers}
    {parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po consumed : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript X ⟨.K, mods⟩) (wf : X.WellFormed .tapscript)
    (output : AmbientKeyOutput X)
    (context : ExecutionContext parent (.c X) env flags pa po consumed)
    (run : Eval (compile (.c X)) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) : CheckedSignature (.c X) env flags consumed := by
  obtain ⟨own, sig, keyBytes, eq, runX, checked⟩ := c_run_frame typed wf run truth
  subst consumed
  have contextX := executionContext_restrict context (active := X)
    (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_append_right _ h)
  obtain ⟨key, hk, keyEq⟩ := output parent env flags pa po own keyBytes (sig :: rest) contextX runX
  rw [keyEq] at checked
  exact ⟨sig, by simp, key, hk, checked⟩

theorem ambientExecution_c {X : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript X ⟨.K, mods⟩) (wf : X.WellFormed .tapscript) :
    AmbientExecutionB (.c X) := by
  intro parent env flags pa po consumed top rest context _bounded run truth
  exact Or.inr (c_success_checked typed wf (keyOutput_of_typed typed wf) context run truth)

theorem c_static {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType .tapscript (.c X) ⟨.B, mods⟩) (wf : (CoreFragment.c X).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.c X) malMods) (nm : malMods.nonMalleable = true) :
    ∃ cm mm, HasType .tapscript X ⟨.K, cm⟩ ∧ X.WellFormed .tapscript ∧
      HasMalleability .tapscript X mm ∧ mm.nonMalleable = true := by
  cases typed with
  | c_wrap typedX =>
    cases mal with
    | c childMal => exact ⟨_, _, typedX, wf, childMal, nm⟩

theorem c_BExecutionPremise (X : CoreFragment) : BExecutionPremise (.c X) := by
  intro mods malMods typed wf mal nm
  obtain ⟨cm, _mm, typedX, wfX, _malX, _nmX⟩ := c_static typed wf mal nm
  exact ambientExecution_c typedX wfX

def RemainingBW : CoreFragment → Prop
  | .and_b _ _ | .or_b _ _ | .thresh _ _ => True
  | _ => False

theorem discharge_compound_keys {fragment : CoreFragment} (old : RemainingBKW fragment)
    (wCases : RemainingBW fragment → BExecutionPremise fragment) : BExecutionPremise fragment := by
  cases fragment <;> simp only [RemainingBKW] at old
  all_goals try contradiction
  case c X => exact c_BExecutionPremise X
  all_goals exact wCases old

theorem ambientExecutionB_from_W {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment malMods) (nm : malMods.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingBW child → BExecutionPremise child) :
    AmbientExecutionB fragment := by
  apply ambientExecutionB_from_KW typed wf mal nm
  intro child bound old
  exact discharge_compound_keys old (remaining child bound)

end LeanMiniscript.Extraction.TapscriptRecovery.CompoundK

namespace LeanMiniscript.Extraction.TapscriptRecovery.WBoolean

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC SignedV BWrappers CompoundK

def booleanNode (isOr : Bool) (X Y : CoreFragment) : CoreFragment :=
  if isOr then .or_b X Y else .and_b X Y

def booleanOpcode (isOr : Bool) : Opcode :=
  if isOr then .OP_BOOLOR else .OP_BOOLAND

def BooleanTruth (isOr : Bool) (a b : StackElement) : Prop :=
  if isOr then castToBool a = true ∨ castToBool b = true
  else castToBool a = true ∧ castToBool b = true

export _root_.LeanMiniscript.Extraction.TapscriptWitness (decode_pair_parts)

theorem decoded_size {bytes : StackElement} {minimal : Bool} {n : Int}
    (decoded : decodeScriptNum bytes minimal maxArithmeticScriptNumBytes = .ok n) :
    bytes.size ≤ maxScriptElementSize := by
  by_cases bound : bytes.size ≤ 4
  · exact Nat.le_trans bound (by decide)
  · have large : bytes.size > 4 := by omega
    simp [decodeScriptNum, maxArithmeticScriptNumBytes, large] at decoded

theorem decoded_nonzero_truth {bytes : StackElement} {minimal : Bool} {n : Int}
    (decoded : decodeScriptNum bytes minimal maxArithmeticScriptNumBytes = .ok n)
    (nonzero : n ≠ 0) : castToBool bytes = true := by
  cases truth : castToBool bytes
  · exact (nonzero (decode_false_zero4 decoded truth)).elim
  · rfl

theorem boolean_single_truth {isOr : Bool} {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] input alt flags ctx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ a b, input = a :: b :: rest ∧ alt = [] ∧
      a.size ≤ maxScriptElementSize ∧ b.size ≤ maxScriptElementSize ∧ BooleanTruth isOr a b := by
  cases isOr
  · change Eval [.op .OP_BOOLAND] _ _ _ _ _ at run
    cases run with
    | booland aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx =>
        obtain ⟨da, db⟩ := decode_pair_parts decoded
        have both : a ≠ 0 ∧ b ≠ 0 := by simpa using truth
        exact ⟨aBytes, bBytes, rfl, rfl, decoded_size da, decoded_size db,
          decoded_nonzero_truth da both.1, decoded_nonzero_truth db both.2⟩
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  · change Eval [.op .OP_BOOLOR] _ _ _ _ _ at run
    cases run with
    | boolor aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx =>
        obtain ⟨da, db⟩ := decode_pair_parts decoded
        have either : a ≠ 0 ∨ b ≠ 0 := by simpa using truth
        refine ⟨aBytes, bBytes, rfl, rfl, decoded_size da, decoded_size db, ?_⟩
        rcases either with ha | hb
        · exact Or.inl (decoded_nonzero_truth da ha)
        · exact Or.inr (decoded_nonzero_truth db hb)
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem boolean_order_truth {isOr : Bool} {order : BaseWOutputOrder}
    {saved result top : StackElement} {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] (order.outputs saved result ++ tail) [] flags ctx
      (.success (top :: rest) [])) (truth : castToBool top = true) :
    tail = rest ∧ saved.size ≤ maxScriptElementSize ∧ result.size ≤ maxScriptElementSize ∧
      BooleanTruth isOr saved result := by
  obtain ⟨a, b, eq, _, ba, bb, h⟩ := boolean_single_truth run truth
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append,
    List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, ba, bb, h⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, bb, ba, by cases isOr <;> simp_all [BooleanTruth, or_comm, and_comm]⟩

theorem boolean_run_frame {isOr : Bool} {X Y : CoreFragment} {mx my : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {consumed : Witness} {top : StackElement} {rest : Stack}
    (typedX : HasType .tapscript X ⟨.B, mx⟩) (typedY : HasType .tapscript Y ⟨.W, my⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (run : Eval (compile (booleanNode isOr X Y)) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder),
      consumed = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs x y ++ rest) []) ∧
      x.size ≤ maxScriptElementSize ∧ y.size ≤ maxScriptElementSize ∧ BooleanTruth isOr x y := by
  have combined : Eval (compile X ++ (compile Y ++ [.op (booleanOpcode isOr)]))
      (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    cases isOr <;> simpa [booleanNode, booleanOpcode, compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨midX, altX, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX _ _ _ _ _ runX
  cases altEqX
  obtain ⟨midY, altY, runY, opRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow Y) tailRun
  obtain ⟨altEqY, effectY⟩ := refinedBaseTypeGuarantee_of_hasType typedY wfY _ _ _ _ _ runY
  cases altEqY
  obtain ⟨argsX, tailX, x, inputX, outputX, _⟩ := effectX.b_inv
  rw [outputX] at effectY runY
  obtain ⟨argsY, tailY, saved, y, order, inputY, outputY⟩ := effectY.w_inv
  obtain ⟨rfl, tailEq⟩ := List.cons.inj inputY
  rw [outputY] at opRun runY
  obtain ⟨rfl, bx, bySize, boolTruth⟩ := boolean_order_truth opRun truth
  have inputEq : consumed.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : consumed = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, witnessEq, ?_, ?_, bx, bySize, boolTruth⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY

def AmbientExecutionW (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po consumed : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContext parent fragment env flags pa po consumed →
    (∀ item ∈ saved :: (consumed.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (consumed.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = true → ExecutionEvidence fragment env flags consumed

export _root_.LeanMiniscript.Extraction.TapscriptWitness (a_run_child)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (s_run_child)

def AmbientExecutionBSaved (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po consumed : Witness) (top : StackElement) (rest : Stack) (saved : StackElement),
    ExecutionContext parent fragment env flags pa po consumed →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [saved] flags env.txCtx
      (.success (top :: rest) [saved]) →
    castToBool top = true → ExecutionEvidence fragment env flags consumed

theorem ambientExecutionW_a {X : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript X ⟨.B, mods⟩) (wf : X.WellFormed .tapscript)
    (execute : AmbientExecutionBSaved X) : AmbientExecutionW (.a X) := by
  intro parent env flags pa po consumed saved top rest order context bounded run truth
  have contextX := executionContext_restrict context (active := X)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
  exact execute parent env flags pa po consumed top rest saved contextX
    (fun item h => bounded item (List.mem_cons_of_mem _ h)) (a_run_child typed wf run) truth

theorem ambientExecutionW_s {X : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript X ⟨.B, mods⟩) (one : mods.o = true) (wf : X.WellFormed .tapscript)
    (execute : AmbientExecutionB X) : AmbientExecutionW (.s X) := by
  intro parent env flags pa po consumed saved top rest order context bounded run truth
  have contextX := executionContext_restrict context (active := X)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
  have boundX : ∀ item ∈ consumed.toInitialStack ++ (saved :: rest), item.size ≤ maxScriptElementSize := by
    intro item h
    apply bounded
    simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using h
  exact execute parent env flags pa po consumed top (saved :: rest) contextX boundX
    (s_run_child typed one wf run).2 truth

inductive WShape : CoreFragment → Prop where
  | a {X : CoreFragment} {mods : CorrectnessModifiers}
      (typed : HasType .tapscript X ⟨.B, mods⟩) : WShape (.a X)
  | s {X : CoreFragment} {mods : CorrectnessModifiers}
      (typed : HasType .tapscript X ⟨.B, mods⟩) (one : mods.o = true) : WShape (.s X)

theorem typed_W_shape {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript fragment ⟨.W, mods⟩) : WShape fragment := by
  generalize typeEq : (⟨.W, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case a_wrap typedX => exact .a typedX
  case s_wrap typedX one => exact .s typedX one
  case and_v typedX typedY branch =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case or_i typedX typedY branch same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case andor typedX d u typedY typedZ branch same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim

def SavedAltTransfer (fragment : CoreFragment) : Prop :=
  ∀ (input output : Stack) (saved : StackElement) (flags : ScriptFlags) (ctx : TxContext),
    Eval (compile fragment) input [saved] flags ctx (.success output [saved]) →
    Eval (compile fragment) input [] flags ctx (.success output [])

theorem saved_execution_of_transfer {X : CoreFragment} (transfer : SavedAltTransfer X)
    (execute : AmbientExecutionB X) : AmbientExecutionBSaved X := by
  intro parent env flags pa po consumed top rest saved context bounded run truth
  exact execute parent env flags pa po consumed top rest context bounded
    (transfer _ _ _ _ _ run) truth

theorem ambientExecutionW_from_smaller_B {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.W, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremise child)
    (transfer : ∀ child, fragment = .a child → SavedAltTransfer child) : AmbientExecutionW fragment := by
  cases typed_W_shape typed with
  | a typedX =>
    cases mal with
    | a malX =>
      exact ambientExecutionW_a typedX wf
        (saved_execution_of_transfer (transfer _ rfl) (ihB _ (by simp) _ _ typedX wf malX nm))
  | s typedX one =>
    cases mal with
    | s malX => exact ambientExecutionW_s typedX one wf (ihB _ (by simp) _ _ typedX wf malX nm)

theorem ambientExecution_boolean {isOr : Bool} {X Y : CoreFragment} {mx my : CorrectnessModifiers}
    (typedX : HasType .tapscript X ⟨.B, mx⟩) (typedY : HasType .tapscript Y ⟨.W, my⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (executeX : AmbientExecutionB X) (executeY : AmbientExecutionW Y)
    (dsat : isOr = true → ∀ env, RawUnsigned (satisfactionCandidates X env).dsat ∧
      RawUnsigned (satisfactionCandidates Y env).dsat) : AmbientExecutionB (booleanNode isOr X Y) := by
  intro parent env flags pa po consumed top rest context bounded run truth
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by, actual⟩ :=
    boolean_run_frame typedX typedY wfX wfY run truth
  subst consumed
  have keysX : ∀ key ∈ X.keys, key ∈ (booleanNode isOr X Y).keys := by
    cases isOr <;> exact fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (booleanNode isOr X Y).keys := by
    cases isOr <;> exact fun _ h => List.mem_append_right _ h
  have locksX : ∀ lock ∈ X.hashLocks, lock ∈ (booleanNode isOr X Y).hashLocks := by
    cases isOr <;> exact fun _ h => List.mem_append_left _ h
  have locksY : ∀ lock ∈ Y.hashLocks, lock ∈ (booleanNode isOr X Y).hashLocks := by
    cases isOr <;> exact fun _ h => List.mem_append_right _ h
  have contextX := executionContext_restrict context keysX locksX (fun _ h => List.mem_append_right _ h)
  have contextY := executionContext_restrict context keysY locksY (fun _ h => List.mem_append_left _ h)
  have boundX : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  have boundY : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    intro item h
    rcases List.mem_cons.mp h with rfl | h
    · exact bx
    · exact boundX item (List.mem_append_right _ h)
  have ex := fun hx => executeX parent env flags pa po left x (right.toInitialStack ++ rest)
    contextX boundX runX hx
  have ey := fun hy => executeY parent env flags pa po right x y rest order contextY boundY runY hy
  have liftX : CheckedSignature X env flags left →
      CheckedSignature (booleanNode isOr X Y) env flags (right ++ left) := by
    rintro ⟨sig, hs, key, hk, checked⟩
    exact ⟨sig, List.mem_append_right _ hs, key, keysX key hk, checked⟩
  have liftY : CheckedSignature Y env flags right →
      CheckedSignature (booleanNode isOr X Y) env flags (right ++ left) := by
    rintro ⟨sig, hs, key, hk, checked⟩
    exact ⟨sig, List.mem_append_left _ hs, key, keysY key hk, checked⟩
  cases isOr
  · obtain ⟨hx, hy⟩ := actual
    rcases ex hx with unsignedX | checkedX
    · rcases ey hy with unsignedY | checkedY
      · exact Or.inl (unsigned_combine unsignedX unsignedY)
      · exact Or.inr (liftY checkedY)
    · exact Or.inr (liftX checkedX)
  · obtain ⟨unsignedDsatX, unsignedDsatY⟩ := dsat rfl env
    rcases actual with hx | hy
    · rcases ex hx with unsignedX | checkedX
      · exact Or.inl (unsigned_select_left_raw
          (unsigned_select_left_raw (unsigned_combine unsignedX unsignedDsatY)))
      · exact Or.inr (liftX checkedX)
    · rcases ey hy with unsignedY | checkedY
      · exact Or.inl (unsigned_select_left_raw
          (unsigned_select_right_raw (unsigned_combine unsignedDsatX unsignedY)))
      · exact Or.inr (liftY checkedY)

theorem and_b_static {X Y : CoreFragment} {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.and_b X Y) ⟨.B, mods⟩)
    (wf : (CoreFragment.and_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.and_b X Y) mm) (nm : mm.nonMalleable = true) :
    ∃ cx cy mx my, HasType .tapscript X ⟨.B, cx⟩ ∧ HasType .tapscript Y ⟨.W, cy⟩ ∧
      X.WellFormed .tapscript ∧ Y.WellFormed .tapscript ∧
      HasMalleability .tapscript X mx ∧ HasMalleability .tapscript Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true := by
  cases typed with
  | and_b typedX typedY =>
    cases mal with
    | and_b malX malY =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      exact ⟨_, _, _, _, typedX, typedY, wf.1, wf.2.1, malX, malY, nx, ny⟩

theorem or_b_static {X Y : CoreFragment} {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.or_b X Y) ⟨.B, mods⟩)
    (wf : (CoreFragment.or_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_b X Y) mm) (nm : mm.nonMalleable = true) :
    ∃ cx cy mx my, HasType .tapscript X ⟨.B, cx⟩ ∧ cx.d = true ∧
      HasType .tapscript Y ⟨.W, cy⟩ ∧ cy.d = true ∧
      X.WellFormed .tapscript ∧ Y.WellFormed .tapscript ∧
      HasMalleability .tapscript X mx ∧ HasMalleability .tapscript Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.e = true ∧ my.e = true ∧
      (mx.s = true ∨ my.s = true) := by
  cases typed with
  | or_b typedX dx typedY dy =>
    cases mal with
    | or_b malX malY =>
      obtain ⟨nx, ny, ex, ey, signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      exact ⟨_, _, _, _, typedX, dx, typedY, dy, wf.1, wf.2, malX, malY, nx, ny, ex, ey,
        Bool.or_eq_true_iff.mp signed⟩

theorem and_b_parent_step {X Y : CoreFragment} {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.and_b X Y) ⟨.B, mods⟩)
    (wf : (CoreFragment.and_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.and_b X Y) mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.and_b X Y) → BExecutionPremise child)
    (transfer : ∀ child, Y = .a child → SavedAltTransfer child) : AmbientExecutionB (.and_b X Y) := by
  obtain ⟨cx, cy, mx, my, tx, ty, wx, wy, hx, hy, nx, ny⟩ := and_b_static typed wf mal nm
  exact ambientExecution_boolean (isOr := false) tx ty wx wy (ihB X (by simp; omega) cx mx tx wx hx nx)
    (ambientExecutionW_from_smaller_B ty wy hy ny
      (fun child smaller => ihB child (by simp_all; omega)) transfer) (by simp)

theorem or_b_parent_step {X Y : CoreFragment} {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.or_b X Y) ⟨.B, mods⟩)
    (wf : (CoreFragment.or_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_b X Y) mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.or_b X Y) → BExecutionPremise child)
    (transfer : ∀ child, Y = .a child → SavedAltTransfer child) : AmbientExecutionB (.or_b X Y) := by
  obtain ⟨cx, cy, mx, my, tx, _dx, ty, _dy, wx, wy, hx, hy, nx, ny, ex, ey, _signed⟩ := or_b_static typed wf mal nm
  exact ambientExecution_boolean (isOr := true) tx ty wx wy (ihB X (by simp; omega) cx mx tx wx hx nx)
    (ambientExecutionW_from_smaller_B ty wy hy ny
      (fun child smaller => ihB child (by simp_all; omega)) transfer)
    (fun _ env => ⟨expressive_rawUnsigned wx tx hx nx ex env, expressive_rawUnsigned wy ty hy ny ey env⟩)

def SavedAltPremise (fragment : CoreFragment) : Prop :=
  ∀ (mods : CorrectnessModifiers) (mm : MalleabilityModifiers),
    HasType .tapscript fragment ⟨.B, mods⟩ → fragment.WellFormed .tapscript →
    HasMalleability .tapscript fragment mm → mm.nonMalleable = true → SavedAltTransfer fragment

theorem transfer_from_W_child {Y : CoreFragment} {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript Y ⟨.W, mods⟩) (wf : Y.WellFormed .tapscript)
    (mal : HasMalleability .tapscript Y mm) (nm : mm.nonMalleable = true)
    (transfer : ∀ child, sizeOf child < sizeOf Y → SavedAltPremise child) :
    ∀ child, Y = .a child → SavedAltTransfer child := by
  intro child eq
  subst Y
  cases typed_W_shape typed with
  | a typedX =>
    cases mal with
    | a malX => exact transfer child (by simp) _ _ typedX wf malX nm

def RemainingBThresh : CoreFragment → Prop
  | .thresh _ _ => True
  | _ => False

theorem ambientExecutionB_from_thresh_and_transfer {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingBThresh child → BExecutionPremise child)
    (transfer : ∀ child, sizeOf child < sizeOf fragment → SavedAltPremise child) : AmbientExecutionB fragment := by
  have childB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremise child := by
    intro child smaller cm hm tc wc hc nc
    exact ambientExecutionB_from_thresh_and_transfer tc wc hc nc
      (fun residual bound h => remaining residual (Nat.le_trans bound (Nat.le_of_lt smaller)) h)
      (fun subchild bound => transfer subchild (Nat.lt_trans bound smaller))
  apply ambientExecutionB_from_W typed wf mal nm
  intro residual bound isRemaining cm hm tc wc hc nc
  cases residual <;> simp only [RemainingBW] at isRemaining
  all_goals try contradiction
  case and_b X Y =>
    obtain ⟨_, _, _, _, _tx, ty, _wx, wy, _hx, hy, _nx, ny⟩ := and_b_static tc wc hc nc
    exact and_b_parent_step tc wc hc nc
      (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
      (transfer_from_W_child ty wy hy ny (fun child smaller => transfer child (by simp_all; omega)))
  case or_b X Y =>
    obtain ⟨_, _, _, _, _tx, _dx, ty, _dy, _wx, wy, _hx, hy, _nx, ny, _ex, _ey, _s⟩ := or_b_static tc wc hc nc
    exact or_b_parent_step tc wc hc nc
      (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
      (transfer_from_W_child ty wy hy ny (fun child smaller => transfer child (by simp_all; omega)))
  case thresh k children => exact remaining _ bound trivial cm hm tc wc hc nc
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.WBoolean
