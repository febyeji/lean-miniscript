import LeanMiniscript.Extraction.TapscriptRecovery.Dissatisfaction

/-! Classify successful executions of B leaves, wrappers, and conditional branches. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.BExecution

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI OrDC Dsat SignedV

theorem branch_B_frame {X Y : CoreFragment} {modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest args tail : Stack} {top resultTop : StackElement}
    (typedY : HasType sc Y ⟨.B, modsY⟩) (wfY : Y.WellFormed sc)
    (inputEq : other.toInitialStack ++ rest = args ++ tail)
    (runX : Eval (compile X) (args ++ tail) [] flags env.txCtx (.success (top :: tail) []))
    (runY : Eval (compile Y) tail [] flags env.txCtx (.success (resultTop :: rest) [])) :
    ∃ left right, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) []) := by
  obtain ⟨right, tailEq⟩ := typed_B_input_frame typedY wfY runY
  have stackEq : other.toInitialStack = args ++ right.toInitialStack := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputEq
  have otherEq : other = right ++ args.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  refine ⟨args.reverse, right, otherEq, ?_, ?_⟩
  · rw [tailEq] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← tailEq]; exact runY

theorem andor_run_B_frame {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {resultTop : StackElement}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.B, modsY⟩) (typedZ : HasType sc Z ⟨.B, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
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
  · obtain ⟨left, right, eq, rx, rz⟩ := branch_B_frame typedZ wfZ inputEq runX runZ
    exact Or.inl ⟨left, right, top, eq, rx, falsehood, rz⟩
  · obtain ⟨left, right, eq, rx, ry⟩ := branch_B_frame typedY wfY inputEq runX runY
    exact Or.inr ⟨left, right, top, eq, rx, truth, ry⟩

theorem ambientExecutionB_andor {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.B, modsY⟩) (typedZ : HasType sc Z ⟨.B, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionBIn sc Y) (executeZ : AmbientExecutionBIn sc Z)
    (unsignedX : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat) :
    AmbientExecutionBIn sc (.andor X Y Z) := by
  intro parent env flags pa po consumed resultTop rest context bounded run outputTruth
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  rcases andor_run_B_frame typedX typedY typedZ wfX wfY wfZ run with
      ⟨left, right, top, eq, _runX, _falsehood, runZ⟩ | ⟨left, right, top, eq, runX, truth, runY⟩
  · subst consumed
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases executeZ parent env flags pa po right resultTop rest contextZ
      (fun item hi => boundAll item (List.mem_append_right _ hi)) runZ outputTruth with unsignedZ | checkedZ
    · exact Or.inl (unsigned_select_right_raw (unsigned_combine (unsignedX env) unsignedZ))
    · exact Or.inr (checkedSignature_mono keysZ inZ checkedZ)
  · subst consumed
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have contextY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases executeX parent env flags pa po left top (right.toInitialStack ++ rest) contextX boundAll runX truth
      with unsignedX | checkedX
    · rcases executeY parent env flags pa po right resultTop rest contextY
        (fun item hi => boundAll item (List.mem_append_right _ hi)) runY outputTruth with unsignedY | checkedY
      · exact Or.inl (unsigned_select_left_raw (unsigned_combine unsignedX unsignedY))
      · exact Or.inr (checkedSignature_mono keysY inY checkedY)
    · exact Or.inr (checkedSignature_mono keysX inX checkedX)

theorem ambientExecutionB_andor_from_children {X Y Z : CoreFragment}
    {modsX modsY modsZ : CorrectnessModifiers} {mods : MalleabilityModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.B, modsY⟩) (typedZ : HasType sc Z ⟨.B, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mods) (nm : mods.nonMalleable = true)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionBIn sc Y) (executeZ : AmbientExecutionBIn sc Z) :
    AmbientExecutionBIn sc (.andor X Y Z) := by
  obtain ⟨mx, _my, _mz, hx, _hy, _hz, nx, _ny, _nz, ex⟩ := andor_malleability_children mal nm
  exact ambientExecutionB_andor typedX typedY typedZ wfX wfY wfZ executeX executeY executeZ
    (expressive_rawUnsigned wfX typedX hx nx ex)

inductive KShapeIn (sc : ScriptContext) : CoreFragment → Prop where
  | pk_k (key : PubKey) : KShapeIn sc (.pk_k key)
  | pk_h (key : PubKey) : KShapeIn sc (.pk_h key)
  | and_v {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.V, mx⟩)
      (typedY : HasType sc Y ⟨.K, my⟩) : KShapeIn sc (.and_v X Y)
  | or_i {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.K, mx⟩)
      (typedY : HasType sc Y ⟨.K, my⟩) : KShapeIn sc (.or_i X Y)
  | andor {X Y Z : CoreFragment} {mx my mz : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩) (d : mx.d = true) (u : mx.u = true)
      (typedY : HasType sc Y ⟨.K, my⟩)
      (typedZ : HasType sc Z ⟨.K, mz⟩) : KShapeIn sc (.andor X Y Z)

abbrev KShape := KShapeIn .tapscript

theorem typed_K_shape {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.K, mods⟩) : KShapeIn sc fragment := by
  generalize typeEq : (⟨.K, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case pk_k key => exact .pk_k key
  case pk_h key => exact .pk_h key
  case and_v typedX typedY _branch =>
    rename_i tyY
    cases tyY with
    | mk base modsY =>
      change BaseType.K = base at baseEq
      subst base
      exact .and_v typedX typedY
  case or_i typedX typedY _branch sameBase =>
    rename_i tyX tyY
    cases tyX with
    | mk baseX modsX =>
      change BaseType.K = baseX at baseEq
      subst baseX
      cases tyY with
      | mk baseY modsY =>
        change BaseType.K = baseY at sameBase
        subst baseY
        exact .or_i typedX typedY
  case andor typedX d u typedY typedZ _branch sameBase =>
    rename_i tyY tyZ
    cases tyY with
    | mk baseY modsY =>
      change BaseType.K = baseY at baseEq
      subst baseY
      cases tyZ with
      | mk baseZ modsZ =>
        change BaseType.K = baseZ at sameBase
        subst baseZ
        exact .andor typedX d u typedY typedZ

def RemainingB : CoreFragment → Prop
  | .older _ | .after _ | .hash256 _ | .ripemd160 _ => True
  | .and_b _ _ | .or_b _ _ | .thresh _ _ => True
  | .d _ | .j _ | .n _ => True
  | .c (.and_v _ _) | .c (.or_i _ _) | .c (.andor _ _ _) => True
  | _ => False

inductive BShapeIn (sc : ScriptContext) : CoreFragment → Prop where
  | zero : BShapeIn sc .zero
  | one : BShapeIn sc .one
  | sha256 (hash : Hash256) : BShapeIn sc (.sha256 hash)
  | hash160 (hash : Hash160) : BShapeIn sc (.hash160 hash)
  | c_pk_k (key : PubKey) : BShapeIn sc (.c (.pk_k key))
  | c_pk_h (key : PubKey) : BShapeIn sc (.c (.pk_h key))
  | multi (k : Nat) (keys : List PubKey) : BShapeIn sc (.multi k keys)
  | multi_a (k : Nat) (keys : List PubKey) : BShapeIn sc (.multi_a k keys)
  | and_v {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.V, mx⟩)
      (typedY : HasType sc Y ⟨.B, my⟩) : BShapeIn sc (.and_v X Y)
  | or_d {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩) (d : mx.d = true) (u : mx.u = true)
      (typedY : HasType sc Y ⟨.B, my⟩) : BShapeIn sc (.or_d X Y)
  | or_i {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩)
      (typedY : HasType sc Y ⟨.B, my⟩) : BShapeIn sc (.or_i X Y)
  | andor {X Y Z : CoreFragment} {mx my mz : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩) (d : mx.d = true) (u : mx.u = true)
      (typedY : HasType sc Y ⟨.B, my⟩)
      (typedZ : HasType sc Z ⟨.B, mz⟩) : BShapeIn sc (.andor X Y Z)
  | remaining {fragment : CoreFragment} (unproved : RemainingB fragment) : BShapeIn sc fragment

abbrev BShape := BShapeIn .tapscript

theorem typed_B_shape {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.B, mods⟩) : BShapeIn sc fragment := by
  generalize typeEq : (⟨.B, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case zero => exact .zero
  case one => exact .one
  case older => exact .remaining trivial
  case after => exact .remaining trivial
  case sha256 hash => exact .sha256 hash
  case hash256 => exact .remaining trivial
  case ripemd160 => exact .remaining trivial
  case hash160 hash => exact .hash160 hash
  case and_v typedX typedY _branch =>
    rename_i tyY
    cases tyY with
    | mk base modsY =>
      change BaseType.B = base at baseEq
      subst base
      exact .and_v typedX typedY
  case and_b => exact .remaining trivial
  case or_b => exact .remaining trivial
  case or_d typedX d u typedY => exact .or_d typedX d u typedY
  case or_i typedX typedY _branch sameBase =>
    rename_i tyX tyY
    cases tyX with
    | mk baseX modsX =>
      change BaseType.B = baseX at baseEq
      subst baseX
      cases tyY with
      | mk baseY modsY =>
        change BaseType.B = baseY at sameBase
        subst baseY
        exact .or_i typedX typedY
  case andor typedX d u typedY typedZ _branch sameBase =>
    rename_i tyY tyZ
    cases tyY with
    | mk baseY modsY =>
      change BaseType.B = baseY at baseEq
      subst baseY
      cases tyZ with
      | mk baseZ modsZ =>
        change BaseType.B = baseZ at sameBase
        subst baseZ
        exact .andor typedX d u typedY typedZ
  case c_wrap typedX =>
    cases typed_K_shape typedX with
    | pk_k key => exact .c_pk_k key
    | pk_h key => exact .c_pk_h key
    | and_v => exact .remaining trivial
    | or_i => exact .remaining trivial
    | andor => exact .remaining trivial
  case d_wrap => exact .remaining trivial
  case j_wrap => exact .remaining trivial
  case n_wrap => exact .remaining trivial
  case thresh => exact .remaining trivial
  case multi => exact .multi _ _
  case multi_a => exact .multi_a _ _

theorem ambientExecutionB_zero : AmbientExecutionBIn sc .zero := by
  intro parent env flags pa po consumed top rest _context _bounded run truth
  have canonical : Eval (compile .zero) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (scriptNum 0 :: (consumed.toInitialStack ++ rest)) []) := by
    apply Eval.pushNum
    exact Eval.done
  have eq := Eval.result_unique run canonical
  have topEq : top = scriptNum 0 := (List.cons.inj (ExecResult.success.inj eq).1).1
  rw [topEq] at truth
  change false = true at truth
  cases truth

theorem ambientExecutionB_one : AmbientExecutionBIn sc .one := by
  intro parent env flags pa po consumed top rest _context _bounded _run _truth
  exact Or.inl ⟨{ witness := [], hasSig := false }, rfl, rfl⟩

theorem no_wellFormed_tapscript_multi (k : Nat) (keys : List PubKey) :
    ¬ (CoreFragment.multi k keys).WellFormed .tapscript := by
  intro wf
  exact wf.1

theorem andor_B_typed_children {X Y Z : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, mods⟩) :
    ∃ mx my mz, HasType sc X ⟨.B, mx⟩ ∧ mx.d = true ∧ mx.u = true ∧
      HasType sc Y ⟨.B, my⟩ ∧ HasType sc Z ⟨.B, mz⟩ := by
  cases typed_B_shape typed with
  | andor tx d u ty tz => exact ⟨_, _, _, tx, d, u, ty, tz⟩
  | remaining impossible => cases impossible

theorem andor_B_parent_step {X Y Z : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, mods⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) malMods) (nm : malMods.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.andor X Y Z) → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc (.andor X Y Z) := by
  obtain ⟨modsX, modsY, modsZ, typedX, _d, _u, typedY, typedZ⟩ := andor_B_typed_children typed
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, _ex⟩ := andor_malleability_children mal nm
  exact ambientExecutionB_andor_from_children typedX typedY typedZ wf.1 wf.2.1 wf.2.2.1 mal nm
    (ihB X (by simp; omega) _ _ typedX wf.1 hx nx)
    (ihB Y (by simp; omega) _ _ typedY wf.2.1 hy ny)
    (ihB Z (by simp; omega) _ _ typedZ wf.2.2.1 hz nz)

theorem ambientExecutionB_from_remaining {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingB child → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc fragment := by
  have childB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremiseIn sc child := by
    intro child smaller cm mm tc wfc mc nmc
    exact ambientExecutionB_from_remaining tc wfc mc nmc
      (fun residual bound isRemaining => remaining residual (Nat.le_trans bound (Nat.le_of_lt smaller)) isRemaining)
  cases typed_B_shape typed with
  | zero => exact ambientExecutionB_zero
  | one => exact ambientExecutionB_one
  | sha256 hash => exact ambientExecution_sha256 hash
  | hash160 hash => exact ambientExecution_hash160 hash
  | c_pk_k key => exact ambientExecution_c_pk_k key
  | c_pk_h key => exact ambientExecution_c_pk_h key
  | multi k keys =>
    cases sc with
    | p2wsh => exact ambientExecution_multi wf
    | tapscript => exact wf.1.elim
  | multi_a k keys =>
    cases sc with
    | p2wsh => exact wf.1.elim
    | tapscript => exact ambientExecution_multi_a k keys wf.2.1 wf.2.2.1
  | and_v typedX typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
    exact ambientExecution_and_v typedX typedY wf.1 wf.2.1
      (ambientExecutionV_from_smaller_B typedX wf.1 hx nx
        (fun child smaller => childB child (Nat.lt_trans smaller (by simp; omega))))
      (childB _ (by simp; omega) _ _ typedY wf.2.1 hy ny)
  | or_d typedX _d _u typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := true) mal nm
    exact ambientExecution_shortCircuit (keep := true) typedX typedY wf.1 wf.2
      (childB _ (by simp; omega) _ _ typedX wf.1 hx nx)
      (childB _ (by simp; omega) _ _ typedY wf.2 hy ny)
      (expressive_rawUnsigned wf.1 typedX hx nx ex)
  | or_i typedX typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
    exact ambientExecution_or_i_B typedX typedY wf.1 wf.2
      (childB _ (by simp; omega) _ _ typedX wf.1 hx nx)
      (childB _ (by simp; omega) _ _ typedY wf.2 hy ny)
  | andor typedX _d _u typedY typedZ => exact andor_B_parent_step typed wf mal nm childB
  | remaining isRemaining => exact remaining _ (Nat.le_refl _) isRemaining _ _ typed wf mal nm
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.BExecution

namespace LeanMiniscript.Extraction.TapscriptRecovery.BLeaves

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Active OrI SignedV BExecution

theorem accepts_hash256_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {h : Hash256} {input rest : Stack} {top : StackElement}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH256,
      .pushData h.bytes, .op .OP_EQUAL] input [] flags txCtx
      (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ preimage, input = preimage :: rest ∧
      (HashLock.hash256 h).Matches preimage := by
  exact _root_.LeanMiniscript.Extraction.TapscriptWitness.hashLock_frame (lock := .hash256 h) bounded run truth

theorem accepts_ripemd160_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {h : Hash160} {input rest : Stack} {top : StackElement}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_RIPEMD160,
      .pushData h.bytes, .op .OP_EQUAL] input [] flags txCtx
      (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ preimage, input = preimage :: rest ∧
      (HashLock.ripemd160 h).Matches preimage := by
  exact _root_.LeanMiniscript.Extraction.TapscriptWitness.hashLock_frame (lock := .ripemd160 h) bounded run truth

theorem ambientExecution_hash256 (hash : Hash256) : AmbientExecutionBIn sc (.hash256 hash) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  obtain ⟨p, eq, matched⟩ := accepts_hash256_inversion bounded run truth
  have consumedEq : consumed = [p] := witness_eq_singleton_of_toInitialStack
    (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [consumedEq]))
    (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  exact Or.inl ⟨{witness := [p], hasSig := false},
    by simp [satisfactionCandidates, hashCandidates, selected, CandidateResult.usable], rfl⟩

theorem ambientExecution_ripemd160 (hash : Hash160) : AmbientExecutionBIn sc (.ripemd160 hash) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  obtain ⟨p, eq, matched⟩ := accepts_ripemd160_inversion bounded run truth
  have consumedEq : consumed = [p] := witness_eq_singleton_of_toInitialStack
    (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [consumedEq]))
    (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  exact Or.inl ⟨{witness := [p], hasSig := false},
    by simp [satisfactionCandidates, hashCandidates, selected, CandidateResult.usable], rfl⟩

theorem older_success_satisfied {n : Nat} {input out alt outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} (valid : validTimelockArg n)
    (run : Eval (compile (.older n)) input alt flags ctx (.success out outAlt)) :
    sequenceSatisfied n ctx := by
  have canonical : decodeScriptNum (scriptNum n) flags.minimalData maxTimelockScriptNumBytes = .ok (n : Int) :=
    (TimelockExecutionFacts.of_validTimelockArg (flags := flags) valid).decoded
  change Eval [.pushNum n, .op .OP_CHECKSEQUENCEVERIFY] input alt flags ctx (.success out outAlt) at run
  cases run with
  | pushNum number rest script' altStack' flags' ctx' result' inner =>
    cases inner with
    | checksequenceverify_success operand m rest' script'' altStack'' flags'' ctx'' result'' decode _nonneg satisfied _final =>
      rw [canonical] at decode
      cases decode
      simpa using satisfied
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
      simp [Opcode.isUpgradeableNop] at upgradable

theorem after_success_satisfied {n : Nat} {input out alt outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} (valid : validTimelockArg n)
    (run : Eval (compile (.after n)) input alt flags ctx (.success out outAlt)) :
    locktimeSatisfied n ctx := by
  have canonical : decodeScriptNum (scriptNum n) flags.minimalData maxTimelockScriptNumBytes = .ok (n : Int) :=
    (TimelockExecutionFacts.of_validTimelockArg (flags := flags) valid).decoded
  change Eval [.pushNum n, .op .OP_CHECKLOCKTIMEVERIFY] input alt flags ctx (.success out outAlt) at run
  cases run with
  | pushNum number rest script' altStack' flags' ctx' result' inner =>
    cases inner with
    | checklocktimeverify_success operand m rest' script'' altStack'' flags'' ctx'' result'' decode _nonneg satisfied _final =>
      rw [canonical] at decode
      cases decode
      simpa using satisfied
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
      simp [Opcode.isUpgradeableNop] at upgradable

theorem ambientExecution_older (n : Nat) (valid : validTimelockArg n) : AmbientExecutionBIn sc (.older n) := by
  intro parent env flags pa po consumed top rest _context _bounded run _truth
  have satisfied := older_success_satisfied valid run
  exact Or.inl ⟨{ witness := [], hasSig := false },
    by simp [satisfactionCandidates, satisfied, CandidateResult.usable], rfl⟩

theorem ambientExecution_after (n : Nat) (valid : validTimelockArg n) : AmbientExecutionBIn sc (.after n) := by
  intro parent env flags pa po consumed top rest _context _bounded run _truth
  have satisfied := after_success_satisfied valid run
  exact Or.inl ⟨{ witness := [], hasSig := false },
    by simp [satisfactionCandidates, satisfied, CandidateResult.usable], rfl⟩

theorem older_BExecutionPremise (n : Nat) : BExecutionPremiseIn sc (.older n) := by
  intro mods malMods _typed wf _mal _nm
  exact ambientExecution_older n wf

theorem after_BExecutionPremise (n : Nat) : BExecutionPremiseIn sc (.after n) := by
  intro mods malMods _typed wf _mal _nm
  exact ambientExecution_after n wf

theorem hash256_BExecutionPremise (hash : Hash256) : BExecutionPremiseIn sc (.hash256 hash) := by
  intro mods malMods _typed _wf _mal _nm
  exact ambientExecution_hash256 hash

theorem ripemd160_BExecutionPremise (hash : Hash160) : BExecutionPremiseIn sc (.ripemd160 hash) := by
  intro mods malMods _typed _wf _mal _nm
  exact ambientExecution_ripemd160 hash

def RemainingBComposite : CoreFragment → Prop
  | .and_b _ _ | .or_b _ _ | .thresh _ _ => True
  | .d _ | .j _ | .n _ => True
  | .c (.and_v _ _) | .c (.or_i _ _) | .c (.andor _ _ _) => True
  | _ => False

theorem discharge_remaining_leaves {fragment : CoreFragment} (old : RemainingB fragment)
    (composite : RemainingBComposite fragment → BExecutionPremiseIn sc fragment) : BExecutionPremiseIn sc fragment := by
  cases fragment <;> simp only [RemainingB] at old
  all_goals try contradiction
  case older n => exact older_BExecutionPremise n
  case after n => exact after_BExecutionPremise n
  case hash256 hash => exact hash256_BExecutionPremise hash
  case ripemd160 hash => exact ripemd160_BExecutionPremise hash
  case c X =>
    have reduced : RemainingBComposite (.c X) := by
      cases X <;> simp_all [RemainingBComposite]
    exact composite reduced
  all_goals exact composite old

theorem ambientExecutionB_from_composite {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingBComposite child → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc fragment := by
  apply ambientExecutionB_from_remaining typed wf mal nm
  intro child bound old
  exact discharge_remaining_leaves old (remaining child bound)

end LeanMiniscript.Extraction.TapscriptRecovery.BLeaves

namespace LeanMiniscript.Extraction.TapscriptRecovery.BWrappers

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat SignedV BLeaves

theorem decode_false_zero4 {operand : StackElement} {minimal : Bool} {value : Int}
    (decoded : decodeScriptNum operand minimal maxArithmeticScriptNumBytes = .ok value)
    (falsehood : castToBool operand = false) : value = 0 := by
  have bound : operand.size ≤ 4 := by
    by_cases bounded : operand.size ≤ 4
    · exact bounded
    · have large : operand.size > 4 := by omega
      simp [decodeScriptNum, maxArithmeticScriptNumBytes, large] at decoded
  rcases operand with ⟨data⟩
  have repr : (⟨data⟩ : ByteArray) = ⟨data.toList.toArray⟩ := by simp
  generalize bytesEq : data.toList = bytes at repr
  rw [repr] at decoded falsehood bound
  change bytes.length ≤ 4 at bound
  change decodeScriptNum ⟨bytes.toArray⟩ minimal 4 = .ok value at decoded
  rcases bytes with _ | ⟨a, tail⟩
  · simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨b, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    have lastFalse := falsehood
    by_cases lastZero : a = 0
    · subst a
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : a = 128 := lastFalse lastZero
      subst a
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨c, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, lastFalse⟩
    by_cases lastZero : b = 0
    · subst b
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : b = 128 := lastFalse lastZero
      subst b
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨d, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, rfl, lastFalse⟩
    by_cases lastZero : c = 0
    · subst c
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : c = 128 := lastFalse lastZero
      subst c
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨e, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, rfl, rfl, lastFalse⟩
    by_cases lastZero : d = 0
    · subst d
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : d = 128 := lastFalse lastZero
      subst d
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  simp at bound

theorem d_success_child {X : CoreFragment} {input rest : Stack} {top : StackElement}
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

theorem d_run_frame {X : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc X ⟨.V, mods⟩) (wf : X.WellFormed sc)
    (run : Eval (compile (.d X)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ active, other = [top] ++ active ∧
      Eval (compile X) (active.toInitialStack ++ (top :: rest)) [] flags env.txCtx (.success (top :: rest) []) := by
  have childRun := d_success_child run truth
  obtain ⟨active, inputEq⟩ := typed_V_input_frame typed wf childRun
  have stackEq : other.toInitialStack = active.toInitialStack ++ [top] := by
    apply List.append_cancel_right
    simpa [List.append_assoc] using inputEq
  have otherEq : other = [top] ++ active := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  exact ⟨active, otherEq, by rw [← inputEq]; exact childRun⟩

theorem ambientExecution_d {X : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc X ⟨.V, mods⟩) (wf : X.WellFormed sc)
    (execute : AmbientExecutionVIn sc X) : AmbientExecutionBIn sc (.d X) := by
  intro parent env flags pa po consumed top rest context bounded run truth
  obtain ⟨active, eq, childRun⟩ := d_run_frame typed wf run truth
  subst consumed
  have inChild : ∀ item ∈ active, item ∈ [top] ++ active := fun _ h => List.mem_append_right _ h
  have childContext := executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) inChild
  have childBound : ∀ item ∈ active.toInitialStack ++ (top :: rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  rcases execute parent env flags pa po active (top :: rest) childContext childBound childRun with unsigned | checked
  · exact Or.inl (unsigned_withSelector unsigned)
  · exact Or.inr (checkedSignature_mono (fun _ h => h) inChild checked)

theorem j_success_child {X : CoreFragment} {input rest : Stack} {top : StackElement}
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

theorem ambientExecution_j {X : CoreFragment} (execute : AmbientExecutionBIn sc X) : AmbientExecutionBIn sc (.j X) := by
  intro parent env flags pa po consumed top rest context bounded run truth
  have childContext := executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  exact execute parent env flags pa po consumed top rest childContext bounded (j_success_child bounded run truth) truth

theorem n_success_child {X : CoreFragment} {input rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.n X)) input [] flags ctx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ value, Eval (compile X) input [] flags ctx (.success (value :: rest) []) ∧ castToBool value = true := by
  change Eval (compile X ++ [.op .OP_0NOTEQUAL]) input [] flags ctx (.success (top :: rest) []) at run
  obtain ⟨mid, midAlt, childRun, normalize⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  cases normalize with
  | zeroNotEqual operand value tail alt script flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      have nonzero : value ≠ 0 := by
        intro eq
        rw [eq] at truth
        change false = true at truth
        cases truth
      refine ⟨operand, childRun, ?_⟩
      cases boolEq : castToBool operand with
      | false => exact (nonzero (decode_false_zero4 decoded boolEq)).elim
      | true => rfl
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem ambientExecution_n {X : CoreFragment} (execute : AmbientExecutionBIn sc X) : AmbientExecutionBIn sc (.n X) := by
  intro parent env flags pa po consumed top rest context bounded run truth
  obtain ⟨value, childRun, childTruth⟩ := n_success_child run truth
  have childContext := executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  exact execute parent env flags pa po consumed value rest childContext bounded childRun childTruth

theorem d_static {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.d X) ⟨.B, mods⟩) (wf : (CoreFragment.d X).WellFormed sc)
    (mal : HasMalleability sc (.d X) malMods) (nm : malMods.nonMalleable = true) :
    ∃ cm mm, HasType sc X ⟨.V, cm⟩ ∧ cm.z = true ∧ X.WellFormed sc ∧
      HasMalleability sc X mm ∧ mm.nonMalleable = true := by
  cases typed with
  | d_wrap typedX zeroArgs =>
    cases mal with
    | d childMal => exact ⟨_, _, typedX, zeroArgs, wf, childMal, nm⟩

theorem j_static {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.j X) ⟨.B, mods⟩) (wf : (CoreFragment.j X).WellFormed sc)
    (mal : HasMalleability sc (.j X) malMods) (nm : malMods.nonMalleable = true) :
    ∃ cm mm, HasType sc X ⟨.B, cm⟩ ∧ cm.n = true ∧ X.WellFormed sc ∧
      HasMalleability sc X mm ∧ mm.nonMalleable = true := by
  cases typed with
  | j_wrap typedX nonzero =>
    cases mal with
    | j childMal => exact ⟨_, _, typedX, nonzero, wf, childMal, nm⟩

theorem n_static {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.n X) ⟨.B, mods⟩) (wf : (CoreFragment.n X).WellFormed sc)
    (mal : HasMalleability sc (.n X) malMods) (nm : malMods.nonMalleable = true) :
    ∃ cm mm, HasType sc X ⟨.B, cm⟩ ∧ X.WellFormed sc ∧
      HasMalleability sc X mm ∧ mm.nonMalleable = true := by
  cases typed with
  | n_wrap typedX =>
    cases mal with
    | n childMal => exact ⟨_, _, typedX, wf, childMal, nm⟩

theorem d_parent_step {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.d X) ⟨.B, mods⟩) (wf : (CoreFragment.d X).WellFormed sc)
    (mal : HasMalleability sc (.d X) malMods) (nm : malMods.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.d X) → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc (.d X) := by
  obtain ⟨cm, mm, typedX, _zeroArgs, wfX, malX, nmX⟩ := d_static typed wf mal nm
  exact ambientExecution_d typedX wfX (ambientExecutionV_from_smaller_B typedX wfX malX nmX
    (fun child smaller => ihB child (Nat.lt_trans smaller (by simp))))

theorem j_parent_step {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.j X) ⟨.B, mods⟩) (wf : (CoreFragment.j X).WellFormed sc)
    (mal : HasMalleability sc (.j X) malMods) (nm : malMods.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.j X) → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc (.j X) := by
  obtain ⟨cm, mm, typedX, _nonzero, wfX, malX, nmX⟩ := j_static typed wf mal nm
  exact ambientExecution_j (ihB X (by simp) cm mm typedX wfX malX nmX)

theorem n_parent_step {X : CoreFragment} {mods : CorrectnessModifiers} {malMods : MalleabilityModifiers}
    (typed : HasType sc (.n X) ⟨.B, mods⟩) (wf : (CoreFragment.n X).WellFormed sc)
    (mal : HasMalleability sc (.n X) malMods) (nm : malMods.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf (CoreFragment.n X) → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc (.n X) := by
  obtain ⟨cm, mm, typedX, wfX, malX, nmX⟩ := n_static typed wf mal nm
  exact ambientExecution_n (ihB X (by simp) cm mm typedX wfX malX nmX)

def RemainingBKW : CoreFragment → Prop
  | .and_b _ _ | .or_b _ _ | .thresh _ _ => True
  | .c (.and_v _ _) | .c (.or_i _ _) | .c (.andor _ _ _) => True
  | _ => False

theorem ambientExecutionB_from_KW {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingBKW child → BExecutionPremiseIn sc child) :
    AmbientExecutionBIn sc fragment := by
  have childB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremiseIn sc child := by
    intro child smaller cm mm tc wfc mc nmc
    exact ambientExecutionB_from_KW tc wfc mc nmc
      (fun residual bound h => remaining residual (Nat.le_trans bound (Nat.le_of_lt smaller)) h)
  apply ambientExecutionB_from_composite typed wf mal nm
  intro residual bound isComposite cm mm tc wfc mc nmc
  cases residual <;> simp only [RemainingBComposite] at isComposite
  all_goals try contradiction
  case d X =>
    exact d_parent_step tc wfc mc nmc
      (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
  case j X =>
    exact j_parent_step tc wfc mc nmc
      (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
  case n X =>
    exact n_parent_step tc wfc mc nmc
      (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
  case c X =>
    have reduced : RemainingBKW (.c X) := by cases X <;> simp_all [RemainingBKW]
    exact remaining _ bound reduced cm mm tc wfc mc nmc
  all_goals exact remaining _ bound isComposite cm mm tc wfc mc nmc
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.BWrappers
