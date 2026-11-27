import LeanMiniscript.Extraction.TapscriptHashWitnessProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.BaseType

/-! Recover a child frame relative to the generated and observed witnesses of
    the same sane root. A recursive call keeps the root material assumptions. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- Material available while inverting a subfragment. Only the consumed part of
    its input comes from the third-party witness; a caller may supply a suffix. -/
structure ExecutionContext (root : SaneFragment .tapscript) (child : CoreFragment)
    (env : SatEnv) (flags : ScriptFlags) (arguments other consumed : Witness) : Prop where
  sound : env.Sound
  version : env.txCtx.sigVersion = .tapscript
  modeled : ModeledContextFlags .tapscript flags
  canonical : satisfy root.checked.fragment env = some arguments
  thirdParty : ThirdPartyWitness root.checked.fragment env.txCtx arguments other
  recover : LocalHashSlotRecovery root.checked.fragment env arguments
  keys : ∀ key ∈ child.keys, key ∈ root.checked.fragment.keys
  locks : ∀ lock ∈ child.hashLocks, lock ∈ root.checked.fragment.hashLocks
  items : ∀ item ∈ consumed, item ∈ other

theorem ExecutionContext.restrict {root child env flags args other consumed}
    (ctx : ExecutionContext root child env flags args other consumed)
    {inner : CoreFragment} {part : Witness} (keys : ∀ k ∈ inner.keys, k ∈ child.keys)
    (locks : ∀ l ∈ inner.hashLocks, l ∈ child.hashLocks) (items : ∀ i ∈ part, i ∈ consumed) :
    ExecutionContext root inner env flags args other part :=
  { ctx with
    keys := fun k hk => ctx.keys k (keys k hk)
    locks := fun l hl => ctx.locks l (locks l hl)
    items := fun i hi => ctx.items i (items i hi) }

theorem ExecutionContext.signature {root child env flags args other consumed}
    (ctx : ExecutionContext root child env flags args other consumed)
    {sig : StackElement} {key : PubKey} (present : key ∈ child.keys) (member : sig ∈ consumed)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    env.signatureFor key = some sig :=
  disclosed_signature_selected ctx.sound ctx.version
    (wellFormed_keySizes _ root.checked.wellFormed) ctx.canonical ctx.thirdParty
    (ctx.items _ member) (ctx.keys _ present) checked

theorem ExecutionContext.preimage {root child env flags args other consumed}
    (ctx : ExecutionContext root child env flags args other consumed)
    {item : StackElement} {lock : HashLock} (present : lock ∈ child.hashLocks)
    (member : item ∈ consumed) (matched : lock.Matches item) :
    env.preimageFor lock = some item :=
  hash_slot_recovery_iff.mp ctx.recover other ctx.thirdParty item (ctx.items _ member)
    lock (ctx.locks _ present) matched

/-- Uniqueness of the consumed satisfaction above an arbitrary suffix. B and W
    must succeed with a true result; V verifies it internally. For K the caller
    supplies the successful check on the pending signature and returned key. -/
def FrameUnique (base : BaseType) (child : CoreFragment) : Prop :=
  ∀ {root env flags arguments other consumed own}, ∀ {mods : CorrectnessModifiers},
    HasType .tapscript child ⟨base, mods⟩ → child.WellFormed .tapscript →
    ExecutionContext root child env flags arguments other consumed →
    satisfy child env = some own → ∀ (rest : Stack),
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    match base with
    | .B => ∀ top, Eval (compile child) (consumed.toInitialStack ++ rest) [] flags env.txCtx
        (.success (top :: rest) []) → castToBool top = true → consumed = own
    | .V => Eval (compile child) (consumed.toInitialStack ++ rest) [] flags env.txCtx
        (.success rest []) → consumed = own
    | .K => ∀ sig key, Eval (compile child) (consumed.toInitialStack ++ rest) [] flags env.txCtx
        (.success (key :: sig :: rest) []) →
        checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key = .ok true →
        consumed = own
    | .W => ∀ saved top (order : BaseWOutputOrder), saved.size ≤ maxScriptElementSize →
        Eval (compile child) (saved :: (consumed.toInitialStack ++ rest)) [] flags env.txCtx
          (.success (order.outputs saved top ++ rest) []) → castToBool top = true → consumed = own

private theorem witness_of_frame {consumed frame : Witness} {rest : Stack}
    (equal : consumed.toInitialStack ++ rest = frame.toInitialStack ++ rest) :
    consumed = frame := by
  simpa [Witness.toInitialStack] using congrArg List.reverse (List.append_cancel_right equal)

theorem frameUnique_c_pk_k (key : PubKey) : FrameUnique .B (.c (.pk_k key)) := by
  intro root env flags args other consumed own _ _ _ ctx generated rest _ top run truth
  obtain ⟨sig, shape, checked⟩ := c_pk_k_frame run truth
  have eq := witness_of_frame (frame := [sig]) shape
  subst consumed
  have lookup := ctx.signature (key := key) (.head _) (.head _) checked
  simpa [satisfy_c_pk_k, lookup, List.singleton] using generated

theorem frameUnique_c_pk_h (key : PubKey) : FrameUnique .B (.c (.pk_h key)) := by
  intro root env flags args other consumed own _ _ _ ctx generated rest _ top run truth
  obtain ⟨sig, pubkey, shape, imageEq, checked⟩ := c_pk_h_frame run truth
  have eq := witness_of_frame (frame := [sig, pubkey]) shape
  subst consumed
  have pubEq := ctx.thirdParty.2.2.2 pubkey (ctx.items _ (by simp))
    key (ctx.keys _ (.head _)) imageEq
  subst pubkey
  have lookup := ctx.signature (key := key) (.head _) (.head _) checked
  simpa [satisfy_c_pk_h, lookup] using generated

theorem frameUnique_hashLock (lock : HashLock) : FrameUnique .B lock.fragment := by
  intro root env flags args other consumed own _ _ _ ctx generated rest bounded top run truth
  obtain ⟨p, shape, matched⟩ := hashLock_frame bounded run truth
  have eq := witness_of_frame (frame := [p]) shape
  subst consumed
  have lookup := ctx.preimage (by cases lock <;> exact .head _) (.head _) matched
  cases lock <;> simpa [HashLock.fragment, lookup, List.singleton] using generated

theorem frameUnique_verify {child : CoreFragment} (unique : FrameUnique .B child) :
    FrameUnique .V (.v child) := by
  intro root env flags args other consumed own mods typed wf ctx generated rest bounded run
  have childTyped : ∃ cm, HasType .tapscript child ⟨.B, cm⟩ := by
    generalize heq : (⟨.V, mods⟩ : MiniType) = ty at typed
    cases typed with | v_wrap h => exact ⟨_, h⟩
  obtain ⟨_, ht⟩ := childTyped
  have unfolded := Miniscript.Eval.compileVerify_success_inverse (compile_balancedControlFlow child) run
  obtain ⟨_, _, inner, verify⟩ := Miniscript.Eval.splitBalancedAppend_success
    (compile_balancedControlFlow child) unfolded
  cases verify with
  | verify_success _ _ _ _ _ _ _ truth done =>
    cases done
    exact unique ht wf (ctx.restrict (fun _ h => h) (fun _ h => h) (fun _ h => h))
      generated rest bounded _ inner truth
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => cases upgradable

/-- The K rule and its checking wrapper describe the same pending signature. -/
theorem frameUnique_key_iff {child : CoreFragment} :
    FrameUnique .K child ↔ FrameUnique .B (.c child) := by
  constructor
  · intro unique root env flags args other consumed own mods typed wf ctx generated rest bounded top run truth
    have keyTyped : ∃ cm, HasType .tapscript child ⟨.K, cm⟩ := by
      generalize parentType : (⟨.B, mods⟩ : MiniType) = ty at typed
      cases typed with | c_wrap childTyped => exact ⟨_, childTyped⟩
    obtain ⟨_, ht⟩ := keyTyped
    change Eval (compile child ++ [.op .OP_CHECKSIG]) _ _ _ _ _ at run
    obtain ⟨mid, alt, inner, check⟩ := Miniscript.Eval.splitBalancedAppend_success
      (compile_balancedControlFlow child) run
    cases check with
    | checksig_success key sig _ _ _ _ _ _ ok done =>
      cases done
      exact unique ht wf (ctx.restrict (fun _ h => h) (fun _ h => h) (fun _ h => h))
        generated rest bounded sig key inner ok
    | checksig_failure _ _ _ _ _ _ _ _ _ done => cases done; contradiction
    | upgradeableNop _ _ _ _ _ _ _ h _ _ => cases h
  · intro unique root env flags args other consumed own mods typed wf ctx generated rest bounded sig key run checked
    have wrapper : ExecutionContext root (.c child) env flags args other consumed :=
      ctx.restrict (fun _ h => h) (fun _ h => h) (fun _ h => h)
    apply unique (.c_wrap typed) wf wrapper generated rest bounded trueElement _ rfl
    exact Eval.append run (Eval.checksigTrue checked Eval.done)

theorem a_run_child {X : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {consumed : Witness} {saved top : StackElement}
    {rest : Stack} {order : BaseWOutputOrder}
    (typed : HasType .tapscript X ⟨.B, mods⟩) (wf : X.WellFormed .tapscript)
    (run : Eval (compile (.a X)) (saved :: (consumed.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) [])) :
    Eval (compile X) (consumed.toInitialStack ++ rest) [saved] flags env.txCtx
      (.success (top :: rest) [saved]) := by
  change Eval (.op .OP_TOALTSTACK :: (compile X ++ [.op .OP_FROMALTSTACK])) _ _ _ _ _ at run
  generalize inputEq : saved :: (consumed.toInitialStack ++ rest) = input at run
  cases run with
  | toAltStack x tail alt script flags ctx result tailRun =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj inputEq
    obtain ⟨mid, midAlt, runX, restore⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) tailRun
    obtain ⟨altEq, _⟩ := refinedBaseTypeGuarantee_of_hasType typed wf _ _ _ _ _ runX
    subst midAlt
    have canonical : Eval [.op .OP_FROMALTSTACK] mid [saved] flags env.txCtx
        (.success (saved :: mid) []) := Eval.fromAltStackNext Eval.done
    have eq := (ExecResult.success.inj (Eval.result_unique restore canonical)).1
    have midEq : mid = top :: rest := by
      cases order <;> simp_all [BaseWOutputOrder.outputs]
    rw [midEq] at runX
    exact runX
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem s_run_child {X : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {consumed : Witness} {saved top : StackElement}
    {rest : Stack} {order : BaseWOutputOrder}
    (typed : HasType .tapscript X ⟨.B, mods⟩) (one : mods.o = true) (wf : X.WellFormed .tapscript)
    (run : Eval (compile (.s X)) (saved :: (consumed.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) [])) :
    (∃ argument, consumed = [argument]) ∧
    Eval (compile X) (consumed.toInitialStack ++ (saved :: rest)) [] flags env.txCtx
      (.success (top :: saved :: rest) []) := by
  change Eval (.op .OP_SWAP :: compile X) _ _ _ _ _ at run
  generalize inputEq : saved :: (consumed.toInitialStack ++ rest) = input at run
  cases run with
  | swap a argument tail alt script flags ctx result runX =>
    obtain ⟨rfl, tailInputEq⟩ := List.cons.inj inputEq
    obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf _ _ _ _ _ runX
    obtain ⟨args, childRest, childTop, argsEq, outEq, matchesArgs⟩ := effect.b_inv
    have len : args.length = 1 := matchesArgs.2 one
    cases args with
    | nil => simp at len
    | cons only remaining =>
      cases remaining with
      | cons _ _ => simp at len
      | nil =>
        simp only [List.singleton_append, List.cons.injEq] at argsEq
        obtain ⟨rfl, rfl⟩ := argsEq
        have eq : tail = rest ∧ childTop = top := by
          cases order <;> simp_all [BaseWOutputOrder.outputs]
        obtain ⟨rfl, rfl⟩ := eq
        have ownEq : consumed = [argument] :=
          witness_eq_singleton_of_toInitialStack (List.append_cancel_right tailInputEq)
        refine ⟨⟨argument, ownEq⟩, ?_⟩
        rw [ownEq]
        simpa [Witness.toInitialStack, outEq] using runX
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem frameUnique_a {child : CoreFragment} (unique : FrameUnique .B child) :
    FrameUnique .W (.a child) := by
  intro root env flags args other consumed own mods typed wf ctx generated rest bounded saved top order _ run truth
  generalize h : (⟨.W, mods⟩ : MiniType) = ty at typed
  cases typed with
  | a_wrap ht =>
    exact unique ht wf (ctx.restrict (fun _ h => h) (fun _ h => h) (fun _ h => h))
      generated rest bounded top (Miniscript.Eval.compile_erase_altStack (a_run_child ht wf run)) truth

theorem frameUnique_s {child : CoreFragment} (unique : FrameUnique .B child) :
    FrameUnique .W (.s child) := by
  intro root env flags args other consumed own mods typed wf ctx generated rest bounded saved top order size run truth
  generalize h : (⟨.W, mods⟩ : MiniType) = ty at typed
  cases typed with
  | s_wrap ht one =>
    apply unique ht wf (ctx.restrict (fun _ h => h) (fun _ h => h) (fun _ h => h))
      generated (saved :: rest) _ top (s_run_child ht one wf run).2 truth
    intro i hi
    rcases List.mem_append.mp hi with ownItem | tail
    · exact bounded _ (List.mem_append_left _ ownItem)
    · rcases List.mem_cons.mp tail with rfl | member
      · exact size
      · exact bounded _ (List.mem_append_right _ member)

/-- Split generated and observed arguments independently at an `and_v` boundary. -/
theorem and_v_decompose {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {arguments other : Witness}
    {top : StackElement} {rest : Stack}
    (typedX : HasType .tapscript X ⟨.V, modsX⟩)
    (typedY : HasType .tapscript Y ⟨.B, modsY⟩)
    (wellFormedX : X.WellFormed .tapscript) (wellFormedY : Y.WellFormed .tapscript)
    (canonical : satisfy (.and_v X Y) env = some arguments)
    (run : Eval (compile (.and_v X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    ∃ witX witY otherX otherY : Witness,
      arguments = witY ++ witX ∧ other = otherY ++ otherX ∧
      satisfy X env = some witX ∧ satisfy Y env = some witY ∧
      Eval (compile X) (otherX.toInitialStack ++ (otherY.toInitialStack ++ rest)) []
        flags env.txCtx (.success (otherY.toInitialStack ++ rest) []) ∧
      Eval (compile Y) (otherY.toInitialStack ++ rest) []
        flags env.txCtx (.success (top :: rest) []) := by
  have satAnd : ((satisfactionCandidates X env).sat.combine
      (satisfactionCandidates Y env).sat).usableWitness? = some arguments := canonical
  obtain ⟨witX, witY, satX, satY, witEq⟩ := CandidateResult.combine_usableWitness_iff.mp satAnd
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, runY⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX
    wellFormedX (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  obtain ⟨argsX, inputEqX, _frameX⟩ := effectX.v_inv
  obtain ⟨altEqY, effectY⟩ := refinedBaseTypeGuarantee_of_hasType typedY
    wellFormedY mid midAlt flags env.txCtx (.success (top :: rest) []) runY
  obtain ⟨argsY, restY, resultY, inputEqY, outputEqY, _frameY⟩ := effectY.b_inv
  injection outputEqY with resultEq restEq
  subst resultEq
  subst restEq
  have stackEq : other.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [inputEqY, List.append_assoc] using inputEqX
  have otherEq : other = argsY.reverse ++ argsX.reverse := by
    have h := congrArg List.reverse stackEq
    simpa [Witness.toInitialStack] using h
  cases altEqX
  refine ⟨witX, witY, argsX.reverse, argsY.reverse, witEq, otherEq, satX, satY, ?_, ?_⟩
  · rw [inputEqX, inputEqY] at runX
    simpa [Witness.toInitialStack] using runX
  · simpa [Witness.toInitialStack, List.reverse_reverse, inputEqY] using runY

theorem frameUnique_and_v {first second : CoreFragment} (left : FrameUnique .V first)
    (right : FrameUnique .B second) : FrameUnique .B (.and_v first second) := by
  intro root env flags args other consumed own mods typed wf ctx generated rest bounded top run truth
  generalize heq : (⟨.B, mods⟩ : MiniType) = ty at typed
  cases typed with
  | @and_v _ _ mx tyY tx ty _ =>
    have baseEq := congrArg MiniType.base heq
    cases tyY with
    | mk base my =>
      change BaseType.B = base at baseEq
      subst base
      obtain ⟨wx, wy, ox, oy, rfl, rfl, sx, sy, rx, ry⟩ :=
        and_v_decompose tx ty wf.1 wf.2.1 generated run
      have cx := ctx.restrict (inner := first) (part := ox)
        (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
        (fun _ h => List.mem_append_right _ h)
      have cy := ctx.restrict (inner := second) (part := oy)
        (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
        (fun _ h => List.mem_append_left _ h)
      rw [Witness.toInitialStack_append, List.append_assoc] at bounded
      have ex := left tx wf.1 cx sx _ bounded rx
      have ey := right ty wf.2.1 cy sy _ (fun i hi => bounded i (List.mem_append_right _ hi))
        top ry truth
      rw [ex, ey]

/-- Key and hash checks joined by verified conjunction, with arbitrary nesting. -/
inductive KeyHashConjunction : CoreFragment → Prop
  | pk_k (key : PubKey) : KeyHashConjunction (.c (.pk_k key))
  | pk_h (key : PubKey) : KeyHashConjunction (.c (.pk_h key))
  | hash (lock : HashLock) : KeyHashConjunction lock.fragment
  | and_v {x y} : KeyHashConjunction x → KeyHashConjunction y →
      KeyHashConjunction (.and_v (.v x) y)

theorem KeyHashConjunction.frameUnique {fragment} (shape : KeyHashConjunction fragment) :
    FrameUnique .B fragment := by
  induction shape with
  | pk_k key => exact frameUnique_c_pk_k key
  | pk_h key => exact frameUnique_c_pk_h key
  | hash lock => exact frameUnique_hashLock lock
  | and_v _ _ left right => exact frameUnique_and_v (frameUnique_verify left) right

/-- Lift a proved B-frame recovery rule through the Core script-path boundary. -/
theorem nonMalleability_of_rootFrameUnique (sane : SaneFragment .tapscript)
    (unique : ∀ {env flags arguments other cm},
      HasType .tapscript sane.checked.fragment ⟨.B, cm⟩ →
      ExecutionContext sane sane.checked.fragment env flags arguments other other →
      env.EncodingSound flags → (∀ item ∈ other.toInitialStack, item.size ≤ maxScriptElementSize) →
      ∀ top, Eval (compile sane.checked.fragment) other.toInitialStack [] flags env.txCtx
        (.success [top] []) → castToBool top = true → other = arguments)
    (bytes scriptPubKey : ByteArray) (suffix : Witness) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (slots : LocalHashSlotRecovery sane.checked.fragment env arguments)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  obtain ⟨bounded, modeled, version, top, alt, evaluated, truth⟩ :=
    tapscript_bounded_accepts_of_coreVerifyScript sane bytes scriptPubKey suffix env flags ctx
      oracles keyPath other serialized spend run accepted
  obtain ⟨_, _, typed⟩ := sane.validMiniscript
  have ordinary := satisfyFinal_some_satisfy generated
  have context : ExecutionContext sane sane.checked.fragment env flags.script arguments other other :=
    ⟨run.2.2.2.2.2.1, version, modeled, ordinary, third, slots,
      fun _ h => h, fun _ h => h, fun _ h => h⟩
  apply unique typed context run.2.2.2.2.2.2.1 (by simpa [Witness.toInitialStack] using bounded) top _ truth
  simpa using Miniscript.Eval.compile_erase_altStack (fragment := sane.checked.fragment) evaluated

/-- A frame rule valid in every enclosing fragment also holds at the script root. -/
theorem nonMalleability_of_frameUnique (sane : SaneFragment .tapscript)
    (unique : FrameUnique .B sane.checked.fragment)
    (bytes scriptPubKey : ByteArray) (suffix : Witness) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (slots : LocalHashSlotRecovery sane.checked.fragment env arguments)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  apply nonMalleability_of_rootFrameUnique sane _ bytes scriptPubKey suffix env flags ctx oracles
    keyPath arguments other serialized spend run generated third slots accepted
  intro env flags args observed cm typed context _ bounded top evaluated truth
  exact unique typed sane.checked.wellFormed context context.canonical [] (by simpa using bounded)
    top (by simpa using evaluated) truth

/-- A third party cannot change the witness for a sane conjunction of key checks and hash locks. -/
theorem nonMalleability_keyHashConjunction (sane : SaneFragment .tapscript)
    (shape : KeyHashConjunction sane.checked.fragment)
    (bytes scriptPubKey : ByteArray) (suffix : Witness) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (slots : LocalHashSlotRecovery sane.checked.fragment env arguments)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments :=
  nonMalleability_of_frameUnique sane shape.frameUnique bytes scriptPubKey suffix env flags ctx
    oracles keyPath arguments other serialized spend run generated third slots accepted

end LeanMiniscript.Extraction.TapscriptWitness
