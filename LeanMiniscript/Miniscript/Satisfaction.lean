import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.SatisfactionEnvironment
import LeanMiniscript.Miniscript.SatisfactionCandidates

/-! Recursive satisfaction generation and public witness projections. -/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Construct the BIP 379 key row. `keyTail` is empty for `pk_k` and contains
    the revealed key for `pk_h`; the signature remains first in serialized
    witness order so it lies below the K fragment's own arguments at runtime. -/
def keyCandidates (key : PubKey) (keyTail : Witness)
    (env : SatEnv) : CandidatePair where
  sat := match env.signatureFor key with
    | none => .impossible
    | some signature => .usable (signature :: keyTail) true
  dsat := .usable (falseElement :: keyTail) false

/-- Construct a hashlock row. A matching preimage is selectable when
    available. The canonical nonpreimage dissatisfaction remains available
    for recursive semantics but is always marked DONTUSE by BIP 379. -/
def hashCandidates (lock : HashLock) (env : SatEnv) : CandidatePair where
  sat := match env.preimageFor lock with
    | none => .impossible
    | some preimage => .usable [preimage] false
  dsat := .dontUse [env.nonPreimageFor lock] false .canonical

/-- One legacy multisignature key contributes either its available signature
    or an empty dissatisfaction block. Choices stay in source key order so
    equal-cost exact-count selection prefers earlier keys. -/
def legacyMultiKeyChoice (key : PubKey) (env : SatEnv) : CandidatePair where
  sat := match env.signatureFor key with
    | none => .impossible
    | some signature => .usable [signature] true
  dsat := .usable [] false

/-- Convert the exact-count DP witness into legacy CHECKMULTISIG wire order.
    The DP combines source-order choices into reverse order, so signatures are
    reversed once and the canonical historical dummy is prepended. Selection
    metadata is preserved and the common dummy contributes to final cost. -/
def finalizeLegacyMulti : CandidateResult → CandidateResult
  | .impossible => .impossible
  | .candidate candidate => .candidate {
      candidate with
      witness := falseElement :: candidate.witness.reverse }

/-- Construct BIP 379 legacy `multi` candidates. Raw invalid thresholds and
    key lists above the consensus limit have no candidates. -/
def legacyMultiCandidates (threshold : Nat) (keys : List PubKey)
    (env : SatEnv) : CandidatePair :=
  if threshold = 0 ∨ keys.length < threshold ∨
      maxPubKeysPerMultiSig < keys.length then {}
  else
    let choices := keys.map (fun key => legacyMultiKeyChoice key env)
    { sat := finalizeLegacyMulti
        (CandidatePair.selectExactly threshold choices)
      dsat := .usable (List.replicate (threshold + 1) falseElement) false }

/-- Shared candidate-level guard for threshold literals used by arithmetic
    compilation. It combines the BIP arity relation with the exact four-byte
    Script-number decoding evidence needed by later execution proofs. -/
def candidateThresholdValid (threshold arity : Nat) : Prop :=
  threshold ≠ 0 ∧ threshold ≤ arity ∧ ArithmeticScriptNatSafe threshold

instance (threshold arity : Nat) :
    Decidable (candidateThresholdValid threshold arity) := by
  unfold candidateThresholdValid
  infer_instance

/-- Recover the exact threshold decode from the shared candidate guard. -/
theorem CandidateThresholdValid.decode
    {threshold arity : Nat}
    (valid : candidateThresholdValid threshold arity)
    (minimalData : Bool) :
    decodeScriptNum (scriptNat threshold) minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat threshold) :=
  valid.2.2.decode minimalData

/-- One Tapscript `multi_a` key contributes its signature when available and
    the canonical empty signature otherwise. Source-order exact-count
    composition directly produces the CHECKSIG/CHECKSIGADD wire order. -/
def multiAKeyChoice (key : PubKey) (env : SatEnv) : CandidatePair where
  sat := match env.signatureFor key with
    | none => .impossible
    | some signature => .usable [signature] true
  dsat := .usable [falseElement] false

/-- Construct BIP 379 `multi_a` candidates. Unlike legacy `multi`, Tapscript
    has no 20-key consensus bound; the shared arity and arithmetic threshold
    guard is the only candidate-level restriction. -/
def multiACandidates (threshold : Nat) (keys : List PubKey)
    (env : SatEnv) : CandidatePair :=
  if candidateThresholdValid threshold keys.length then
    let choices := keys.map (fun key => multiAKeyChoice key env)
    { sat := CandidatePair.selectExactly threshold choices
      dsat := .usable (List.replicate keys.length falseElement) false }
  else
    {}

mutual
/-- Compute the candidate pair for every Core fragment row. Semantically
    unavailable sides and failed threshold/multisignature candidate guards are
    represented explicitly as impossible. -/
@[simp] def satisfactionCandidates : CoreFragment → SatEnv → CandidatePair
  | .zero, _ => { dsat := .usable [] false }
  | .one, _ => { sat := .usable [] false }
  | .pk_k key, env => keyCandidates key [] env
  | .pk_h key, env => keyCandidates key [key.bytes] env
  | .older n, env =>
      { sat := if sequenceSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | .after n, env =>
      { sat := if locktimeSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | .sha256 hash, env => hashCandidates (.sha256 hash) env
  | .hash256 hash, env => hashCandidates (.hash256 hash) env
  | .ripemd160 hash, env => hashCandidates (.ripemd160 hash) env
  | .hash160 hash, env => hashCandidates (.hash160 hash) env
  | .and_v first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      { sat := firstCandidates.sat.combine secondCandidates.sat
        dsat := (firstCandidates.sat.combine secondCandidates.dsat).markNonCanonical }
  | .and_b first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      let canonical := firstCandidates.dsat.combine secondCandidates.dsat
      let firstOvercomplete :=
        (firstCandidates.dsat.combine secondCandidates.sat).markOvercomplete
      let secondOvercomplete :=
        (firstCandidates.sat.combine secondCandidates.dsat).markOvercomplete
      { sat := firstCandidates.sat.combine secondCandidates.sat
        dsat := (canonical.select firstOvercomplete).select secondOvercomplete }
  | .or_b first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      let firstSatisfaction := firstCandidates.sat.combine secondCandidates.dsat
      let secondSatisfaction := firstCandidates.dsat.combine secondCandidates.sat
      let overcomplete :=
        (firstCandidates.sat.combine secondCandidates.sat).markOvercomplete
      { sat := (firstSatisfaction.select secondSatisfaction).select overcomplete
        dsat := firstCandidates.dsat.combine secondCandidates.dsat }
  | .or_c first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      { sat := firstCandidates.sat.select
          (firstCandidates.dsat.combine secondCandidates.sat) }
  | .or_d first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      { sat := firstCandidates.sat.select
          (firstCandidates.dsat.combine secondCandidates.sat)
        dsat := firstCandidates.dsat.combine secondCandidates.dsat }
  | .or_i first second, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      { sat := (firstCandidates.sat.withSelector trueElement).select
          (secondCandidates.sat.withSelector falseElement)
        dsat := (firstCandidates.dsat.withSelector trueElement).select
          (secondCandidates.dsat.withSelector falseElement) }
  | .andor first second third, env =>
      let firstCandidates := satisfactionCandidates first env
      let secondCandidates := satisfactionCandidates second env
      let thirdCandidates := satisfactionCandidates third env
      { sat := (firstCandidates.sat.combine secondCandidates.sat).select
          (firstCandidates.dsat.combine thirdCandidates.sat)
        dsat := (firstCandidates.dsat.combine thirdCandidates.dsat).select
          ((firstCandidates.sat.combine secondCandidates.dsat).markNonCanonical) }
  | .thresh threshold fragments, env =>
      if candidateThresholdValid threshold fragments.length then
        let children := satisfactionCandidatesList fragments env
        let states := CandidatePair.countCandidates children
        { sat := CandidatePair.selectExactly threshold children
          dsat := CandidatePair.thresholdDissatisfaction threshold states }
      else
        {}
  | .multi threshold keys, env => legacyMultiCandidates threshold keys env
  | .multi_a threshold keys, env => multiACandidates threshold keys env
  | .c fragment, env => satisfactionCandidates fragment env
  | .a fragment, env => satisfactionCandidates fragment env
  | .s fragment, env => satisfactionCandidates fragment env
  | .v fragment, env => { sat := (satisfactionCandidates fragment env).sat }
  | .n fragment, env => satisfactionCandidates fragment env
  | .d fragment, env =>
      { sat := (satisfactionCandidates fragment env).sat.withSelector trueElement
        dsat := .usable [falseElement] false }
  | .j fragment, env =>
      { sat := (satisfactionCandidates fragment env).sat
        dsat := (CandidateResult.usable [falseElement] false).select
          ((satisfactionCandidates fragment env).dsat
            |>.requireNonemptyRuntimeTop
            |>.markNonCanonical) }

/-- Compute child candidate pairs without hiding recursive fragment calls
    behind a higher-order list operation. -/
@[simp] def satisfactionCandidatesList :
    List CoreFragment → SatEnv → List CandidatePair
  | [], _ => []
  | fragment :: fragments, env =>
      satisfactionCandidates fragment env ::
        satisfactionCandidatesList fragments env
end

@[simp] theorem satisfactionCandidatesList_eq_map
    (fragments : List CoreFragment) (env : SatEnv) :
    satisfactionCandidatesList fragments env =
      fragments.map (fun fragment => satisfactionCandidates fragment env) := by
  induction fragments with
  | nil => rfl
  | cons fragment fragments ih => simp [ih]

/-- Project the usable satisfaction candidate. This is the leaf/composition
    projection only; final HASSIG policy remains a later step. -/
def satisfy (fragment : CoreFragment) (env : SatEnv) : Option Witness :=
  (satisfactionCandidates fragment env).sat.usableWitness?

/-- Return the final BIP 379 satisfaction only when the selected usable
    candidate has HASSIG. Selection is not repeated after this policy gate. -/
def satisfyFinal (fragment : CoreFragment) (env : SatEnv) : Option Witness :=
  (satisfactionCandidates fragment env).sat.finalWitness?

/-- Project the usable dissatisfaction candidate. Canonical hash
    dissatisfactions are deliberately absent here because their raw candidates
    are DONTUSE. -/
def dissatisfy (fragment : CoreFragment) (env : SatEnv) : Option Witness :=
  (satisfactionCandidates fragment env).dsat.usableWitness?

/-- The paired candidate API is the source for ordinary satisfaction
    projection. -/
theorem satisfactionCandidates_sat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat.usableWitness? =
      satisfy fragment env := by
  rfl

/-- Every final witness is the ordinary selected satisfaction witness. -/
theorem satisfyFinal_some_satisfy {fragment : CoreFragment} {env : SatEnv}
    {witness : Witness} (selected : satisfyFinal fragment env = some witness) :
    satisfy fragment env = some witness := by
  exact CandidateResult.finalWitness?_some_usableWitness selected

/-- Successful final projection exposes the selected usable HASSIG candidate. -/
theorem satisfyFinal_some_candidate {fragment : CoreFragment} {env : SatEnv}
    {witness : Witness} (selected : satisfyFinal fragment env = some witness) :
    ∃ candidate,
      (satisfactionCandidates fragment env).sat = .candidate candidate ∧
      candidate.status = .usable ∧
      candidate.hasSig = true ∧
      candidate.witness = witness := by
  exact (CandidateResult.finalWitness?_eq_some_iff _ _).mp selected

/-- The paired candidate API is the single source for public dissatisfaction. -/
theorem satisfactionCandidates_dsat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).dsat.usableWitness? =
      dissatisfy fragment env := by
  rfl

end LeanMiniscript.Miniscript
