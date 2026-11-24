import LeanMiniscript.Extraction.TapscriptWitnessProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.ExecutionDecomposition
import LeanMiniscript.Miniscript.SatisfactionCandidateProofs

/-!
# Tapscript witness uniqueness for `multi_a`

Accepted execution consumes one signature slot per key and exactly the
threshold number of nonempty signatures. The generated witness has the same
slot structure. `ThirdPartyWitness` and distinct keys force each accepted
signature into its canonical position; equality of the nonempty counts then
forces equality of every slot.

The Core-to-witness theorem specializes the existing compiled-spend premises
to sane `multi_a` fragments. The general `TapscriptNonMalleability` obligation
remains unproved.
-/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- A size-zero stack element is the canonical empty element. -/
theorem eq_falseElement_of_size_zero {sig : StackElement} (size : sig.size = 0) :
    sig = falseElement := by
  have emptyList : sig.data.toList = [] :=
    List.eq_nil_of_length_eq_zero size
  cases sig with
  | mk data =>
      have empty : data = #[] := by
        cases data with
        | mk list =>
            cases list with
            | nil => simp
            | cons head tail => simp at emptyList
      subst empty
      rfl

/-- In Tapscript a false checked signature is the empty element. -/
theorem eq_falseElement_of_checkSigWithEncoding_false {flags : ScriptFlags}
    {txCtx : TxContext} {sig pubkey : StackElement}
    (version : txCtx.sigVersion = .tapscript)
    (sigFalse : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig pubkey =
      .ok false) :
    sig = falseElement := by
  unfold checkSigWithEncoding at sigFalse
  cases encoded : checkSigEncodingFor flags txCtx.sigVersion sig pubkey with
  | error error => simp [encoded] at sigFalse
  | ok _ =>
      cases checked : checkedVerifySigFor checkSig checkSchnorrSig txCtx sig pubkey
      with
      | error error => simp [encoded, checked] at sigFalse
      | ok valid =>
          simp only [encoded, checked] at sigFalse
          cases valid with
          | true => simp at sigFalse
          | false =>
              rw [version] at sigFalse
              simp only [↓reduceIte] at sigFalse
              have sizeZero : sig.size = 0 := by
                by_cases nonempty : (sig.size != 0) = true
                · simp [nonempty] at sigFalse
                · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at nonempty
                  simpa using nonempty
              exact eq_falseElement_of_size_zero sizeZero

/-- In Tapscript a true checked signature is nonempty. -/
theorem nonempty_of_checkSigWithEncoding_true {flags : ScriptFlags}
    {ctx : TxContext} {sig pubkey : StackElement}
    (version : ctx.sigVersion = .tapscript)
    (sigOK : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey =
      .ok true) :
    sig ≠ falseElement := by
  intro empty
  have checkedFalse : checkedVerifySigFor checkSig checkSchnorrSig ctx falseElement
      pubkey = .ok false := by
    unfold checkedVerifySigFor
    rw [version]
    have size0 : (falseElement : StackElement).size = 0 := rfl
    simp [size0]
  unfold checkSigWithEncoding at sigOK
  rw [empty] at sigOK
  cases encoded : checkSigEncodingFor flags ctx.sigVersion falseElement pubkey with
  | error error => simp [encoded] at sigOK
  | ok _ =>
      simp only [encoded, checkedFalse] at sigOK
      rw [version] at sigOK
      repeat' split at sigOK
      all_goals simp_all

/-- The per-slot contract of a `multi_a` signature slot: empty, or a checked
valid signature for the slot's key. -/
def sigSlot (flags : ScriptFlags) (ctx : TxContext) (sig : StackElement)
    (key : PubKey) : Prop :=
  sig = falseElement ∨
    checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key.bytes = .ok true

/-- The number of nonempty slots of a signature list. -/
def validCount (sigs : List StackElement) : Nat :=
  (sigs.filter (· ≠ falseElement)).length

/-- Every slot of a zipped signature/key list satisfies the `multi_a`
contract, expressed by `List.all`. -/
theorem slots_all_of_forall {flags : ScriptFlags} {ctx : TxContext}
    {args : List StackElement} {keys : List PubKey}
    (slots : ∀ slot ∈ List.zip args keys, sigSlot flags ctx slot.1 slot.2) :
    (List.zip args keys).all (fun slot =>
      slot.1 = falseElement ||
        verifySigFor checkSig checkSchnorrSig ctx slot.1 slot.2.bytes) = true := by
  rw [List.all_eq_true]
  intro slot member
  rcases slots slot member with empty | valid
  · simp [empty]
  · simp only [Bool.or_eq_true]
    exact Or.inr (verifySigFor_of_checkSigWithEncoding valid)

/-- The canonical count decode of a `scriptNat` accumulator. -/
theorem decodeCheckSigAddCount_scriptNat {flags : ScriptFlags} {ctx : TxContext}
    {count : Nat} (version : ctx.sigVersion = .tapscript)
    (bound : count < maxArithmeticScriptNatExclusive) :
    decodeCheckSigAddCount flags ctx (scriptNat count) = .ok (count : Int) := by
  unfold decodeCheckSigAddCount
  simp only [version, ne_eq, not_true_eq_false, ↓reduceIte]
  exact decodeScriptNum_scriptNat_of_lt bound flags.minimalData

/-- A CHECKSIGADD tail running on a canonical count accumulator consumes one
signature slot per key and adds the number of nonempty slots to the
accumulator. -/
theorem checkSigAddTail_slots {keys : List PubKey}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript) :
    ∀ {count : Nat} {stack finalStack finalAlt altStack : Stack},
    count + keys.length < maxArithmeticScriptNatExclusive →
    Eval (compileCheckSigAddTail keys) (scriptNat count :: stack) altStack
      flags ctx (.success finalStack finalAlt) →
    ∃ args rest, stack = args ++ rest ∧
      finalStack = scriptNat (count + validCount args) :: rest ∧
      args.length = keys.length ∧
      ∀ slot ∈ List.zip args keys, sigSlot flags ctx slot.1 slot.2 := by
  induction keys with
  | nil =>
      intro count stack finalStack finalAlt altStack bound run
      have equal := Eval.result_unique run (Eval.done (altStack := altStack))
      cases equal
      refine ⟨[], stack, by simp, ?_, by simp, by simp⟩
      simp [validCount]
  | cons key keys ih =>
      intro count stack finalStack finalAlt altStack bound run
      simp only [List.length_cons] at bound
      have combined : Eval ([.pushData key, .op .OP_CHECKSIGADD] ++
          compileCheckSigAddTail keys) (scriptNat count :: stack) altStack flags
          ctx (.success finalStack finalAlt) := by
        simpa [compileCheckSigAddTail] using run
      have pushScript : Eval [.pushData key] (scriptNat count :: stack) altStack
          flags ctx (.success (key :: scriptNat count :: stack) altStack) :=
        Eval.pushDataNext Eval.done
      obtain ⟨afterPush, afterPushAlt, pushRun, checkRun⟩ :=
        LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) combined
      have pushEq := Eval.result_unique pushRun pushScript
      cases pushEq
      cases stack with
      | nil =>
          cases checkRun <;> simp_all [Opcode.isUpgradeableNop]
      | cons signature rest =>
          cases checkRun with
          | checksigadd_success pubkey countBytes sig decodedCount rest' script'
              altStack' flags' ctx' result' decodeOK sigOK tailRun =>
              have decodeCanon : decodeCheckSigAddCount flags ctx (scriptNat count) =
                  .ok (count : Int) :=
                decodeCheckSigAddCount_scriptNat version
                  (by omega : count < maxArithmeticScriptNatExclusive)
              rw [decodeCanon] at decodeOK
              have countEq : (count : Int) = decodedCount := by
                cases decodeOK
                rfl
              rw [← countEq] at tailRun
              have accEq : scriptNum ((count : Int) + 1) = scriptNat (count + 1) := by
                have castEq : ((count + 1 : Nat) : Int) = (count : Int) + 1 := by omega
                simp [scriptNat, castEq]
              rw [accEq] at tailRun
              obtain ⟨args', rest'', restEq, finalEq, lengthEq, slots⟩ :=
                ih (count := count + 1) (by omega) tailRun
              have nonempty : signature ≠ falseElement :=
                nonempty_of_checkSigWithEncoding_true version sigOK
              have vcCons : validCount (signature :: args') = validCount args' + 1 := by
                simp only [validCount, List.filter]
                simp [nonempty]
              refine ⟨signature :: args', rest'', ?_, ?_, ?_, ?_⟩
              · simp [restEq]
              · rw [finalEq, vcCons]
                have addEq : count + 1 + validCount args' =
                    count + (validCount args' + 1) := by omega
                rw [addEq]
              · simp [lengthEq]
              · intro slot member
                simp only [List.zip_cons_cons, List.mem_cons] at member
                rcases member with head | tail
                · rw [head]
                  exact Or.inr sigOK
                · exact slots slot tail
          | checksigadd_failure pubkey countBytes sig decodedCount rest' script'
              altStack' flags' ctx' result' decodeOK sigFalse tailRun =>
              have decodeCanon : decodeCheckSigAddCount flags ctx (scriptNat count) =
                  .ok (count : Int) :=
                decodeCheckSigAddCount_scriptNat version
                  (by omega : count < maxArithmeticScriptNatExclusive)
              rw [decodeCanon] at decodeOK
              have countEq : (count : Int) = decodedCount := by
                cases decodeOK
                rfl
              rw [← countEq] at tailRun
              have accEq : scriptNum (count : Int) = scriptNat count := rfl
              rw [accEq] at tailRun
              obtain ⟨args', rest'', restEq, finalEq, lengthEq, slots⟩ :=
                ih (count := count) (by omega) tailRun
              have empty : signature = falseElement :=
                eq_falseElement_of_checkSigWithEncoding_false version sigFalse
              have vcCons : validCount (signature :: args') = validCount args' := by
                simp only [validCount, List.filter]
                simp [empty]
              refine ⟨signature :: args', rest'', ?_, ?_, ?_, ?_⟩
              · simp [restEq]
              · rw [finalEq, vcCons]
              · simp [lengthEq]
              · intro slot member
                simp only [List.zip_cons_cons, List.mem_cons] at member
                rcases member with head | tail
                · rw [head]
                  exact Or.inl empty
                · exact slots slot tail
          | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
              simp [Opcode.isUpgradeableNop] at upgradable

/-- CHECKSIGADD tails contain no control-flow delimiters. -/
private theorem compileCheckSigAddTail_balanced (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append (.append (.atom (by simp [NonConditional]))
        (.atom (by simp [NonConditional]))) ih

/-- Assembly after the first CHECKSIG of a `multi_a` body: the CHECKSIGADD
tail and the terminal `OP_NUMEQUAL` force the consumed slots and the exact
threshold count. -/
private theorem multiA_finish
    {k : Nat} {firstKey : PubKey} {keys : List PubKey}
    {flags : ScriptFlags} {txCtx : TxContext} {other : Witness}
    {sig top : StackElement} {finalAlt : Stack}
    {headCount : Nat} {rest' : Stack}
    (version : txCtx.sigVersion = .tapscript)
    (threshold : validThreshold k (keys.length + 1))
    (keyBound : keys.length + 1 ≤ MAX_PUBKEYS_PER_MULTI_A)
    (stackEq : other.toInitialStack = sig :: rest')
    (headSlot : sigSlot flags txCtx sig firstKey)
    (headVC : (if sig = falseElement then 0 else 1) = headCount)
    (truth : castToBool top = true)
    (inner2 : Eval (compileCheckSigAddTail keys ++ [.pushNum ↑k, .op .OP_NUMEQUAL])
      (scriptNat headCount :: rest') [] flags txCtx (.success [top] finalAlt)) :
    ∃ sigs, other.toInitialStack = sigs ∧ sigs.length = keys.length + 1 ∧
      (List.zip sigs (firstKey :: keys)).all (fun slot =>
        slot.1 = falseElement ||
          verifySigFor checkSig checkSchnorrSig txCtx slot.1 slot.2.bytes) ∧
      (sigs.filter (· ≠ falseElement)).length = k := by
  have maxBound : MAX_PUBKEYS_PER_MULTI_A < maxArithmeticScriptNatExclusive := by decide
  obtain ⟨thresholdLow, thresholdHigh⟩ := threshold
  have headBound : headCount ≤ 1 := by
    rw [← headVC]
    by_cases empty : sig = falseElement <;> simp [empty]
  obtain ⟨mid, midAlt, tailRun, finalRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
      (compileCheckSigAddTail_balanced keys) inner2
  obtain ⟨tailArgs, tailRest, restEq, finalEq, lengthEq, slots⟩ :=
    checkSigAddTail_slots version (by omega) tailRun
  rw [finalEq] at finalRun
  cases finalRun with
  | pushNum n rest0 script0 altStack0 flags0 ctx0 result0 inner3 =>
      cases inner3 with
      | numequal aBytes bBytes a b rest2 script2 altStack2 flags2 ctx2 result2
          decodePair inner4 =>
          cases inner4 with
          | empty lastStack lastAlt lastFlags lastCtx =>
              have vcLe : validCount tailArgs ≤ tailArgs.length :=
                List.length_filter_le _ _
              have decodeBelow : decodeScriptNum
                  (scriptNat (headCount + validCount tailArgs)) flags.minimalData
                  maxArithmeticScriptNumBytes =
                  .ok ((headCount + validCount tailArgs : Nat) : Int) :=
                decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
              have decodeTop : decodeScriptNum (scriptNum (↑k : Int))
                  flags.minimalData maxArithmeticScriptNumBytes =
                  .ok (k : Int) :=
                decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
              unfold decodeBinaryScriptNums at decodePair
              simp only [decodeBelow, decodeTop, bind, Except.bind, pure,
                Except.pure] at decodePair
              cases decodePair
              have eqTrue : ((k : Int) == ((headCount + validCount tailArgs : Nat) : Int)) =
                  true := by
                cases cmp : ((k : Int) == ((headCount + validCount tailArgs : Nat) : Int)) with
                | true => rfl
                | false =>
                    rw [boolToElement, cmp] at truth
                    simp [castToBool, falseElement] at truth
              have kEq : k = headCount + validCount tailArgs := by
                have eqInt : (k : Int) = (headCount + validCount tailArgs : Int) :=
                  beq_iff_eq.mp eqTrue
                omega
              refine ⟨sig :: tailArgs, ?_, ?_, ?_, ?_⟩
              · rw [stackEq, restEq]
                simp
              · simp [lengthEq]
              · apply slots_all_of_forall
                intro slot member
                simp only [List.zip_cons_cons, List.mem_cons] at member
                rcases member with head | tail
                · rw [head]
                  exact headSlot
                · exact slots slot tail
              · have vcTotal : validCount (sig :: tailArgs) =
                    headCount + validCount tailArgs := by
                  rw [← headVC]
                  by_cases empty : sig = falseElement
                  · rw [empty]
                    simp only [validCount]
                    rw [List.filter_cons_of_neg (a := falseElement) (by decide)]
                    simp
                  · simp only [validCount]
                    rw [List.filter_cons_of_pos (a := sig) (by simp [empty])]
                    simp [empty, Nat.add_comm]
                show validCount (sig :: tailArgs) = k
                rw [vcTotal, ← kEq]
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
          simp [Opcode.isUpgradeableNop] at upgradable

/-- An accepted `multi_a` witness has one initial-stack slot per key, each
empty or valid for its key, with exactly `k` nonempty slots. The threshold
and key-count bounds keep the accumulator within ScriptNum limits. -/
theorem accepts_multi_a_inversion
    (k : Nat) (keys : List PubKey)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (other : Witness) (flags : ScriptFlags) (txCtx : TxContext)
    (accepts : Accepts .tapscript (compile (.multi_a k keys)) other flags txCtx) :
    ∃ sigs, other.toInitialStack = sigs ∧ sigs.length = keys.length ∧
      (List.zip sigs keys).all (fun slot =>
        slot.1 = falseElement ||
          verifySigFor checkSig checkSchnorrSig txCtx slot.1 slot.2.bytes) ∧
      (sigs.filter (· ≠ falseElement)).length = k := by
  obtain ⟨_modeled, version, top, finalAlt, executed, truth⟩ := accepts
  have sigVersion : txCtx.sigVersion = .tapscript := version
  unfold Executes at executed
  generalize stackEq : other.toInitialStack = stack at executed
  cases keys with
  | nil =>
      obtain ⟨one, zero⟩ := threshold
      simp only [List.length_nil] at zero
      omega
  | cons firstKey keys =>
      have scriptEq : compile (.multi_a k (firstKey :: keys)) =
          ([.pushData firstKey.bytes, .op .OP_CHECKSIG] ++
            compileCheckSigAddTail keys) ++ [.pushNum ↑k, .op .OP_NUMEQUAL] := by
        simp [compile, compileWithKeyHash, compileCheckSigAdd]
      rw [scriptEq] at executed
      cases executed with
      | pushData data rest initStack altStack flags ctx result inner =>
          cases inner with
          | checksig_success pubkey sig rest' script' altStack' flags' ctx'
              result' sigOK inner2 =>
              have accOne : (trueElement : StackElement) = scriptNat 1 := rfl
              rw [accOne] at inner2
              rw [← stackEq]
              exact multiA_finish sigVersion threshold keyCount stackEq
                (Or.inr sigOK)
                (by simp [nonempty_of_checkSigWithEncoding_true sigVersion sigOK])
                truth inner2
          | checksig_failure pubkey sig rest' script' altStack' flags' ctx'
              result' sigFalse inner2 =>
              have accZero : (falseElement : StackElement) = scriptNat 0 := rfl
              rw [accZero] at inner2
              rw [← stackEq]
              exact multiA_finish sigVersion threshold keyCount stackEq
                (Or.inl (eq_falseElement_of_checkSigWithEncoding_false sigVersion
                  sigFalse))
                (by simp [eq_falseElement_of_checkSigWithEncoding_false sigVersion
                  sigFalse])
                truth inner2
          | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
              simp [Opcode.isUpgradeableNop] at upgradable


/-- Destructure a map equality with a singleton suffix. -/
private theorem map_eq_snoc {keys : List PubKey} {children : List CandidatePair}
    {child : CandidatePair} {f : PubKey → CandidatePair}
    (eq : keys.map f = children ++ [child]) :
    ∃ keys₀ key, keys = keys₀ ++ [key] ∧ keys₀.map f = children ∧ f key = child := by
  induction keys generalizing children with
  | nil => simp at eq
  | cons first rest ih =>
      cases children with
      | nil =>
          simp at eq
          obtain ⟨firstEq, restNil⟩ := eq
          exact ⟨[], first, by simp [restNil], by simp, firstEq⟩
      | cons c cs =>
          injection eq with firstEq restEq
          obtain ⟨rest₀, key, restEq2, csEq, keyEq⟩ := ih restEq
          exact ⟨first :: rest₀, key, by simp [restEq2],
            by simp [firstEq, csEq], keyEq⟩

/-- The sat witness of a `multiAKeyChoice` row is the environment signature. -/
theorem multiAKeyChoice_sat_usableWitness {env : SatEnv} {key : PubKey}
    {witness : Witness}
    (selected : (multiAKeyChoice key env).sat.usableWitness? = some witness) :
    ∃ sig, env.signatureFor key = some sig ∧ witness = [sig] := by
  unfold multiAKeyChoice at selected
  cases sigSel : env.signatureFor key with
  | none => simp [sigSel, CandidateResult.usableWitness?] at selected
  | some sig =>
      simp only [sigSel] at selected
      refine ⟨sig, rfl, ?_⟩
      simp only [CandidateResult.usable, CandidateResult.usableWitness?] at selected
      injection selected with witnessEq
      exact witnessEq.symm

/-- The dsat witness of a `multiAKeyChoice` row is the canonical empty
signature. -/
theorem multiAKeyChoice_dsat_usableWitness {env : SatEnv} {key : PubKey}
    {witness : Witness}
    (selected : (multiAKeyChoice key env).dsat.usableWitness? = some witness) :
    witness = [falseElement] := by
  unfold multiAKeyChoice at selected
  simp only [CandidateResult.usable, CandidateResult.usableWitness?] at selected
  injection selected with witnessEq
  exact witnessEq.symm

/-- A traced exact-count witness of `multi_a` choices decomposes into one
slot per key in source order: the canonical empty element, or the
environment-selected signature for that key. Exactly `count` slots are
nonempty. -/
theorem multiA_slots_of_trace {env : SatEnv} (sound : env.Sound)
    {keys : List PubKey} {count : Nat} {frames : List Witness} {witness : Witness}
    (trace : CandidatePair.ChoiceTrace (keys.map (fun key => multiAKeyChoice key env)) count
      frames witness) :
    ∃ slots, witness.reverse = slots ∧ slots.length = keys.length ∧
      (∀ slot ∈ List.zip slots keys,
        slot.1 = falseElement ∨ env.signatureFor slot.2 = some slot.1) ∧
      (slots.filter (· ≠ falseElement)).length = count := by
  generalize childrenEq : keys.map (fun key => multiAKeyChoice key env) = choices
    at trace
  induction trace generalizing keys with
  | nil =>
      have keysNil : keys = [] := by
        cases keys with
        | nil => rfl
        | cons first rest => simp [List.map_cons] at childrenEq
      subst keysNil
      refine ⟨[], rfl, by simp, by simp, by simp⟩
  | sat trace selected ih =>
      rename_i children count' frames' witness' child childWitness
      obtain ⟨keys₀, key, keysEq, innerEq, childEq⟩ := map_eq_snoc childrenEq
      subst childEq
      obtain ⟨slots₀, reverseEq, lengthEq, form, countEq⟩ := ih innerEq
      obtain ⟨sig, sigSel, witnessEq⟩ := multiAKeyChoice_sat_usableWitness selected
      have nonempty : sig ≠ falseElement := by
        intro empty
        have valid := sound.signatureValid sigSel
        rw [empty] at valid
        exact absurd valid (by simp [sound.emptySignatureInvalid key])
      refine ⟨slots₀ ++ [sig], ?_, ?_, ?_, ?_⟩
      · simp [Witness.combine, witnessEq, reverseEq]
      · simp [lengthEq, keysEq]
      · intro slot member
        rw [keysEq, List.zip_append (l₁ := slots₀) (r₁ := [sig]) (l₂ := keys₀)
          (r₂ := [key]) lengthEq] at member
        rcases List.mem_append.mp member with left | right
        · exact form slot left
        · simp only [List.zip, List.zipWith, List.mem_singleton] at right
          subst right
          exact Or.inr sigSel
      · simp only [List.filter_append]
        have filterSig : List.filter (· ≠ falseElement) [sig] = [sig] :=
          List.filter_cons_of_pos (a := sig) (by simp [nonempty])
        rw [filterSig]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  | dsat trace selected ih =>
      rename_i children count' frames' witness' child childWitness
      obtain ⟨keys₀, key, keysEq, innerEq, childEq⟩ := map_eq_snoc childrenEq
      subst childEq
      obtain ⟨slots₀, reverseEq, lengthEq, form, countEq⟩ := ih innerEq
      have witnessEq := multiAKeyChoice_dsat_usableWitness selected
      refine ⟨slots₀ ++ [falseElement], ?_, ?_, ?_, ?_⟩
      · simp [Witness.combine, witnessEq, reverseEq]
      · simp [lengthEq, keysEq]
      · intro slot member
        rw [keysEq, List.zip_append (l₁ := slots₀) (r₁ := [falseElement])
          (l₂ := keys₀) (r₂ := [key]) lengthEq] at member
        rcases List.mem_append.mp member with left | right
        · exact form slot left
        · simp only [List.zip, List.zipWith, List.mem_singleton] at right
          subst right
          exact Or.inl rfl
      · simp only [List.filter_append]
        have filterEmpty : List.filter (· ≠ falseElement) [falseElement] = [] :=
          List.filter_cons_of_neg (a := falseElement) (by decide)
        rw [filterEmpty]
        simp only [List.append_nil]
        exact countEq

/-- The canonical `multi_a` satisfaction decomposes into one slot per key. -/
theorem satisfyFinal_multi_a {env : SatEnv} (sound : env.Sound)
    {k : Nat} {keys : List PubKey} {arguments : Witness}
    (generated : satisfyFinal (.multi_a k keys) env = some arguments) :
    ∃ slots, arguments.reverse = slots ∧ slots.length = keys.length ∧
      (∀ slot ∈ List.zip slots keys,
        slot.1 = falseElement ∨ env.signatureFor slot.2 = some slot.1) ∧
      (slots.filter (· ≠ falseElement)).length = k := by
  simp only [satisfyFinal, satisfactionCandidates, multiACandidates] at generated
  by_cases guard : candidateThresholdValid k keys.length
  · simp only [guard, ↓reduceIte] at generated
    have satUsable := CandidateResult.finalWitness?_some_usableWitness generated
    obtain ⟨frames, trace⟩ := CandidatePair.selectExactly_choiceTrace satUsable
    obtain ⟨slots, reverseEq, lengthEq, form, countEq⟩ :=
      multiA_slots_of_trace sound trace
    exact ⟨slots, by rw [reverseEq], lengthEq, form, countEq⟩
  · simp only [guard, ↓reduceIte, CandidateResult.finalWitness?]
      at generated
    cases generated

/-- The zipped pair at a valid index is a member of the zip. -/
theorem mem_zip_getElem {l : List StackElement} {l' : List PubKey} {i : Nat}
    (lengthEq : l.length = l'.length) (hi : i < l.length) :
    (l[i], l'[i]'(by omega)) ∈ List.zip l l' := by
  have zipGet : (List.zip l l')[i]'(by simp [List.length_zip, lengthEq]; omega) =
      (l[i], l'[i]'(by omega)) := List.getElem_zip
  rw [← zipGet]
  exact List.getElem_mem _

/-- A pointwise subset relation between slot lists bounds the nonempty
count. -/
theorem filter_length_le_of_subset {sigA sigB : List StackElement}
    (lengthEq : sigA.length = sigB.length)
    (subset : ∀ i (hi : i < sigA.length), sigA[i] ≠ falseElement →
      sigB[i]'(by omega) = sigA[i]) :
    (sigA.filter (· ≠ falseElement)).length ≤
      (sigB.filter (· ≠ falseElement)).length := by
  induction sigA generalizing sigB with
  | nil => simp
  | cons a restA ih =>
      cases sigB with
      | nil => simp at lengthEq
      | cons b restB =>
          simp only [List.length_cons] at lengthEq
          have subsetTail : ∀ i (hi : i < restA.length), restA[i] ≠ falseElement →
              restB[i]'(by omega) = restA[i] := by
            intro i hi nonempty
            have step := subset (i + 1) (by simp only [List.length_cons]; omega)
              nonempty
            rwa [List.getElem_cons_succ] at step
          have tailLe := ih (by omega) subsetTail
          by_cases emptyA : a = falseElement
          · by_cases emptyB : b = falseElement
            · rw [emptyA, emptyB]
              have tA : List.filter (· ≠ falseElement) (falseElement :: restA) =
                  List.filter (· ≠ falseElement) restA :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              have tB : List.filter (· ≠ falseElement) (falseElement :: restB) =
                  List.filter (· ≠ falseElement) restB :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              rw [tA, tB]
              exact tailLe
            · rw [emptyA]
              have tA : List.filter (· ≠ falseElement) (falseElement :: restA) =
                  List.filter (· ≠ falseElement) restA :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              have tB : List.filter (· ≠ falseElement) (b :: restB) =
                  b :: List.filter (· ≠ falseElement) restB :=
                List.filter_cons_of_pos (a := b) (by simpa using emptyB)
              rw [tA, tB]
              simp only [List.length_cons]
              omega
          · have headEq : b = a := by
              have h0 := subset 0 (by simp only [List.length_cons]; omega) emptyA
              rwa [List.getElem_cons_zero] at h0
            have nonemptyB : b ≠ falseElement := headEq ▸ emptyA
            subst b
            have tA : List.filter (· ≠ falseElement) (a :: restA) =
                a :: List.filter (· ≠ falseElement) restA :=
              List.filter_cons_of_pos (a := a) (by simpa using emptyA)
            have tB : List.filter (· ≠ falseElement) (a :: restB) =
                a :: List.filter (· ≠ falseElement) restB :=
              List.filter_cons_of_pos (a := a) (by simpa using nonemptyB)
            rw [tA, tB]
            simp only [List.length_cons]
            omega

/-- Two slot lists in the pointwise subset relation with equal nonempty
counts are equal. -/
theorem multiA_eq_of_subset_count {sigA sigB : List StackElement}
    (lengthEq : sigA.length = sigB.length)
    (subset : ∀ i (hi : i < sigA.length), sigA[i] ≠ falseElement →
      sigB[i]'(by omega) = sigA[i])
    (countEq : (sigA.filter (· ≠ falseElement)).length =
      (sigB.filter (· ≠ falseElement)).length) :
    sigA = sigB := by
  induction sigA generalizing sigB with
  | nil =>
      cases sigB with
      | nil => rfl
      | cons b restB => simp at lengthEq
  | cons a restA ih =>
      cases sigB with
      | nil => simp at lengthEq
      | cons b restB =>
          simp only [List.length_cons] at lengthEq
          have subsetTail : ∀ i (hi : i < restA.length), restA[i] ≠ falseElement →
              restB[i]'(by omega) = restA[i] := by
            intro i hi nonempty
            have step := subset (i + 1) (by simp only [List.length_cons]; omega)
              nonempty
            rwa [List.getElem_cons_succ] at step
          by_cases emptyA : a = falseElement
          · by_cases emptyB : b = falseElement
            · rw [emptyA, emptyB]
              rw [emptyA, emptyB] at countEq
              have tA : List.filter (· ≠ falseElement) (falseElement :: restA) =
                  List.filter (· ≠ falseElement) restA :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              have tB : List.filter (· ≠ falseElement) (falseElement :: restB) =
                  List.filter (· ≠ falseElement) restB :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              rw [tA, tB] at countEq
              exact congrArg (falseElement :: ·) (ih (by omega) subsetTail countEq)
            · exfalso
              rw [emptyA] at countEq
              have tA : List.filter (· ≠ falseElement) (falseElement :: restA) =
                  List.filter (· ≠ falseElement) restA :=
                List.filter_cons_of_neg (a := falseElement) (by decide)
              have tB : List.filter (· ≠ falseElement) (b :: restB) =
                  b :: List.filter (· ≠ falseElement) restB :=
                List.filter_cons_of_pos (a := b) (by simpa using emptyB)
              rw [tA, tB] at countEq
              simp only [List.length_cons] at countEq
              have leTail := filter_length_le_of_subset (by omega) subsetTail
              omega
          · have headEq : b = a := by
              have h0 := subset 0 (by simp only [List.length_cons]; omega) emptyA
              rwa [List.getElem_cons_zero] at h0
            have nonemptyB : b ≠ falseElement := headEq ▸ emptyA
            subst b
            have tA : List.filter (· ≠ falseElement) (a :: restA) =
                a :: List.filter (· ≠ falseElement) restA :=
              List.filter_cons_of_pos (a := a) (by simpa using emptyA)
            have tB : List.filter (· ≠ falseElement) (a :: restB) =
                a :: List.filter (· ≠ falseElement) restB :=
              List.filter_cons_of_pos (a := a) (by simpa using nonemptyB)
            rw [tA, tB] at countEq
            simp only [List.length_cons] at countEq
            have countTail : (List.filter (· ≠ falseElement) restA).length =
                (List.filter (· ≠ falseElement) restB).length := by omega
            exact congrArg (a :: ·) (ih (by omega) subsetTail countTail)

/-- Uniqueness for `multi_a`: the accepted slot list equals the canonical
slot list. `ThirdPartyWitness` clause 2 places every valid slot inside
`arguments`; clause 1 and key uniqueness (NoDuplicateKeys) force each valid
slot to its own key's position. -/
theorem unique_multi_a {env : SatEnv} {flags : ScriptFlags}
    {k : Nat} {keys : List PubKey} {arguments other : Witness}
    (sound : env.Sound)
    (noDup : keys.Nodup)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (accepts : Accepts .tapscript (compile (.multi_a k keys)) other flags env.txCtx)
    (generated : satisfyFinal (.multi_a k keys) env = some arguments)
    (thirdParty : ThirdPartyWitness (.multi_a k keys) env.txCtx arguments other) :
    other = arguments := by
  obtain ⟨sigsO, stackEq, lengthO, allO, countO⟩ :=
    accepts_multi_a_inversion k keys threshold keyCount other flags env.txCtx accepts
  obtain ⟨slotsC, argsRevEq, lengthC, formC, countC⟩ :=
    satisfyFinal_multi_a sound generated
  obtain ⟨noCross, sigMem, _locks, _images⟩ := thirdParty
  have argsEq : arguments = slotsC.reverse := by
    have rev := congrArg List.reverse argsRevEq
    simp only [List.reverse_reverse] at rev
    exact rev
  have lengthOC : sigsO.length = slotsC.length := by omega
  have subsetPoint : ∀ i (hi : i < sigsO.length), sigsO[i] ≠ falseElement →
      slotsC[i]'(by omega) = sigsO[i] := by
    intro i hi nonempty
    have pairMem : (sigsO[i], keys[i]'(by omega)) ∈ List.zip sigsO keys :=
      mem_zip_getElem lengthO hi
    have verified : verifySigFor checkSig checkSchnorrSig env.txCtx sigsO[i]
        (keys[i]'(by omega)).bytes = true := by
      have orTrue := (List.all_eq_true.mp allO) _ pairMem
      by_cases empty : sigsO[i] = falseElement
      · exact absurd empty nonempty
      · simp only [empty, decide_false, Bool.false_or] at orTrue
        exact orTrue
    have otherMem : sigsO[i] ∈ other := by
      have initialMem : sigsO[i] ∈ other.toInitialStack := by
        rw [stackEq]
        exact List.getElem_mem _
      exact List.mem_reverse.mp initialMem
    have keyMem : keys[i]'(by omega) ∈ CoreFragment.keys (.multi_a k keys) := by
      simp only [CoreFragment.keys]
      exact List.getElem_mem _
    have inArgs : sigsO[i] ∈ arguments := sigMem _ otherMem _ keyMem verified
    rw [argsEq] at inArgs
    have inSlotsC : sigsO[i] ∈ slotsC := List.mem_reverse.mp inArgs
    obtain ⟨j, hj, sjEq⟩ := List.getElem_of_mem inSlotsC
    have pairMemJ : (slotsC[j], keys[j]'(by omega)) ∈ List.zip slotsC keys :=
      mem_zip_getElem lengthC hj
    rcases formC _ pairMemJ with emptyC | selectedC
    · exact absurd (sjEq ▸ emptyC) nonempty
    · have validJ : verifySigFor checkSig checkSchnorrSig env.txCtx slotsC[j]
          (keys[j]'(by omega)).bytes = true :=
        sound.signatureValid selectedC
      rw [sjEq] at validJ
      by_cases ijEq : i = j
      · subst ijEq
        exact sjEq
      · exfalso
        have distinct : keys[i]'(by omega) ≠ keys[j]'(by omega) := by
          intro keyEq
          exact ijEq ((List.getElem_inj noDup).mp keyEq)
        exact noCross _ otherMem _ keyMem _
          (by simp only [CoreFragment.keys]; exact List.getElem_mem _) distinct
          verified validJ
  have slotsEq : sigsO = slotsC :=
    multiA_eq_of_subset_count lengthOC subsetPoint (by rw [countO, countC])
  have otherEq : other = sigsO.reverse := by
    have stackEq' : other.reverse = sigsO := stackEq
    have back : other = other.reverse.reverse := (List.reverse_reverse other).symm
    rw [stackEq'] at back
    exact back
  rw [otherEq, slotsEq, argsEq]

/-- Core acceptance of a third-party witness for `multi_a` forces equality
with the generated final satisfaction under the original compiled-spend
premises. Sanity supplies the threshold and key-count bounds and distinct
keys; `CompiledScriptRun` supplies environment soundness. -/
theorem nonMalleability_multi_a
    (sane : SaneFragment .tapscript) (k : Nat) (keys : List PubKey)
    (fragmentEq : sane.checked.fragment = .multi_a k keys)
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray)
    (env : SatEnv) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (thirdParty : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  have accepts := tapscript_accepts_of_coreVerifyScript sane bytes scriptPubKey
    suffix env flags ctx oracles keyPath other serialized spend run accepted
  rw [fragmentEq] at accepts
  rw [fragmentEq] at generated thirdParty
  obtain ⟨_, _, _, _, _, sound, _, _, _⟩ := run
  have noDup : keys.Nodup := by
    have nodup := sane.noDuplicateKeys
    rw [fragmentEq] at nodup
    exact nodup
  have wellFormed := sane.checked.wellFormed
  rw [fragmentEq] at wellFormed
  obtain ⟨_, threshold, keyCount, _⟩ := wellFormed
  exact unique_multi_a sound noDup threshold keyCount accepts generated thirdParty

end LeanMiniscript.Extraction.TapscriptWitness
