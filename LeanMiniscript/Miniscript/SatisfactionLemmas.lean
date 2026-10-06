import LeanMiniscript.Miniscript.Satisfaction

/-! Simplification equations for satisfaction and dissatisfaction of each fragment. -/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/- These equations preserve the original public API while the implementation
   moves to paired candidates. They also keep existing proof scripts independent
   of the representation of `CandidateResult`. -/

@[simp] theorem satisfy_one (env : SatEnv) :
    satisfy .one env = some [] := by
  rfl

@[simp] theorem satisfy_pk_k (key : PubKey) (env : SatEnv) :
    satisfy (.pk_k key) env = List.singleton <$> env.signatureFor key := by
  cases selected : env.signatureFor key <;>
    simp [satisfy, keyCandidates, selected, List.singleton]

@[simp] theorem satisfy_pk_h (key : PubKey) (env : SatEnv) :
    satisfy (.pk_h key) env =
      (fun signature => [signature, key.bytes]) <$> env.signatureFor key := by
  cases selected : env.signatureFor key <;>
    simp [satisfy, keyCandidates, selected]

@[simp] theorem satisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    satisfy (.c (.pk_k key)) env = List.singleton <$> env.signatureFor key := by
  simpa [satisfy] using satisfy_pk_k key env

@[simp] theorem satisfy_c_pk_h (key : PubKey) (env : SatEnv) :
    satisfy (.c (.pk_h key)) env =
      (fun signature => [signature, key.bytes]) <$> env.signatureFor key := by
  simpa [satisfy] using satisfy_pk_h key env

@[simp] theorem satisfy_older (n : Nat) (env : SatEnv) :
    satisfy (.older n) env =
      if sequenceSatisfied n env.txCtx then some [] else none := by
  by_cases available : sequenceSatisfied n env.txCtx <;>
    simp [satisfy, available]

@[simp] theorem satisfy_after (n : Nat) (env : SatEnv) :
    satisfy (.after n) env =
      if locktimeSatisfied n env.txCtx then some [] else none := by
  by_cases available : locktimeSatisfied n env.txCtx <;>
    simp [satisfy, available]

@[simp] theorem satisfy_sha256 (hash : Hash256) (env : SatEnv) :
    satisfy (.sha256 hash) env =
      List.singleton <$> env.preimageFor (.sha256 hash) := by
  cases selected : env.preimageFor (.sha256 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_hash256 (hash : Hash256) (env : SatEnv) :
    satisfy (.hash256 hash) env =
      List.singleton <$> env.preimageFor (.hash256 hash) := by
  cases selected : env.preimageFor (.hash256 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_ripemd160 (hash : Hash160) (env : SatEnv) :
    satisfy (.ripemd160 hash) env =
      List.singleton <$> env.preimageFor (.ripemd160 hash) := by
  cases selected : env.preimageFor (.ripemd160 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_hash160 (hash : Hash160) (env : SatEnv) :
    satisfy (.hash160 hash) env =
      List.singleton <$> env.preimageFor (.hash160 hash) := by
  cases selected : env.preimageFor (.hash160 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem dissatisfy_zero (env : SatEnv) :
    dissatisfy .zero env = some [] := by
  rfl

@[simp] theorem dissatisfy_pk_k (key : PubKey) (env : SatEnv) :
    dissatisfy (.pk_k key) env = some [falseElement] := by
  rfl

@[simp] theorem dissatisfy_pk_h (key : PubKey) (env : SatEnv) :
    dissatisfy (.pk_h key) env = some [falseElement, key.bytes] := by
  rfl

@[simp] theorem dissatisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    dissatisfy (.c (.pk_k key)) env = some [falseElement] := by
  rfl

@[simp] theorem dissatisfy_c_pk_h (key : PubKey) (env : SatEnv) :
    dissatisfy (.c (.pk_h key)) env = some [falseElement, key.bytes] := by
  rfl

@[simp] theorem dissatisfy_sha256 (hash : Hash256) (env : SatEnv) :
    dissatisfy (.sha256 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_hash256 (hash : Hash256) (env : SatEnv) :
    dissatisfy (.hash256 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_ripemd160 (hash : Hash160) (env : SatEnv) :
    dissatisfy (.ripemd160 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_hash160 (hash : Hash160) (env : SatEnv) :
    dissatisfy (.hash160 hash) env = none := by
  rfl

/-! ## Straight-line connective candidates -/

/-- `and_v` executes its V child before its result-producing child. Its only
    Script-valid dissatisfaction is the non-canonical `sat(first) dsat(second)`
    row retained by BIP 379. -/
@[simp] theorem satisfactionCandidates_and_v
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.and_v first second) env = {
      sat := (satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat
      dsat := ((satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).dsat).markNonCanonical } := by
  rfl

@[simp] theorem satisfactionCandidates_and_v_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.and_v first second) env).sat =
      (satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat := by
  rfl

@[simp] theorem satisfactionCandidates_and_v_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.and_v first second) env).dsat =
      ((satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).dsat).markNonCanonical := by
  rfl

@[simp] theorem satisfy_and_v
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.and_v first second) env =
      ((satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_and_v
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.and_v first second) env =
      (((satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).dsat).markNonCanonical).usableWitness? := by
  rfl

/-- `and_b` retains its canonical double dissatisfaction and both non-canonical
    overcomplete alternatives. The two binary selections are deliberately a
    left fold because candidate selection has observable left-biased ties. -/
@[simp] theorem satisfactionCandidates_and_b
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.and_b first second) env = {
      sat := (satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat
      dsat := (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).select
        (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat).markOvercomplete)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markOvercomplete) } := by
  rfl

@[simp] theorem satisfactionCandidates_and_b_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.and_b first second) env).sat =
      (satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat := by
  rfl

@[simp] theorem satisfactionCandidates_and_b_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.and_b first second) env).dsat =
      (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).select
        (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat).markOvercomplete)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markOvercomplete) := by
  rfl

@[simp] theorem satisfy_and_b
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.and_b first second) env =
      ((satisfactionCandidates first env).sat.combine
        (satisfactionCandidates second env).sat).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_and_b
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.and_b first second) env =
      ((((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).select
        (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat).markOvercomplete)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markOvercomplete)).usableWitness? := by
  rfl

/-- `or_b` chooses between its two canonical one-true paths and the
    non-canonical overcomplete double-satisfaction path, again in fixed left-fold
    order. Its only dissatisfaction is the double dissatisfaction. -/
@[simp] theorem satisfactionCandidates_or_b
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.or_b first second) env = {
      sat := (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).markOvercomplete)
      dsat := (satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat } := by
  rfl

@[simp] theorem satisfactionCandidates_or_b_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_b first second) env).sat =
      (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).markOvercomplete) := by
  rfl

@[simp] theorem satisfactionCandidates_or_b_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_b first second) env).dsat =
      (satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat := by
  rfl

@[simp] theorem satisfy_or_b
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.or_b first second) env =
      ((((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).markOvercomplete)).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_or_b
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.or_b first second) env =
      ((satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat).usableWitness? := by
  rfl

/-! ## Conditional connective candidates -/

/-- `or_c` either satisfies its first child and skips the V child, or
    dissatisfies the first child and satisfies the V child. A V result has no
    dissatisfaction. -/
@[simp] theorem satisfactionCandidates_or_c
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.or_c first second) env = {
      sat := (satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat) } := by
  rfl

@[simp] theorem satisfactionCandidates_or_c_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_c first second) env).sat =
      (satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat) := by
  rfl

@[simp] theorem satisfactionCandidates_or_c_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_c first second) env).dsat = .impossible := by
  rfl

@[simp] theorem satisfy_or_c
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.or_c first second) env =
      ((satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_or_c
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.or_c first second) env = none := by
  rfl

/-- `or_d` has the same two satisfaction paths as `or_c`, while its exact
    dissatisfaction combines both child dissatisfactions. -/
@[simp] theorem satisfactionCandidates_or_d
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.or_d first second) env = {
      sat := (satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)
      dsat := (satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat } := by
  rfl

@[simp] theorem satisfactionCandidates_or_d_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_d first second) env).sat =
      (satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat) := by
  rfl

@[simp] theorem satisfactionCandidates_or_d_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_d first second) env).dsat =
      (satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat := by
  rfl

@[simp] theorem satisfy_or_d
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.or_d first second) env =
      ((satisfactionCandidates first env).sat.select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).sat)).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_or_d
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.or_d first second) env =
      ((satisfactionCandidates first env).dsat.combine
        (satisfactionCandidates second env).dsat).usableWitness? := by
  rfl

/-- `or_i` appends the canonical selector corresponding to each branch before
    choosing between otherwise complete child candidates. -/
@[simp] theorem satisfactionCandidates_or_i
    (first second : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.or_i first second) env = {
      sat := ((satisfactionCandidates first env).sat.withSelector
          trueElement).select
        ((satisfactionCandidates second env).sat.withSelector falseElement)
      dsat := ((satisfactionCandidates first env).dsat.withSelector
          trueElement).select
        ((satisfactionCandidates second env).dsat.withSelector falseElement) } := by
  rfl

@[simp] theorem satisfactionCandidates_or_i_sat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_i first second) env).sat =
      ((satisfactionCandidates first env).sat.withSelector trueElement).select
        ((satisfactionCandidates second env).sat.withSelector falseElement) := by
  rfl

@[simp] theorem satisfactionCandidates_or_i_dsat
    (first second : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.or_i first second) env).dsat =
      ((satisfactionCandidates first env).dsat.withSelector trueElement).select
        ((satisfactionCandidates second env).dsat.withSelector falseElement) := by
  rfl

@[simp] theorem satisfy_or_i
    (first second : CoreFragment) (env : SatEnv) :
    satisfy (.or_i first second) env =
      (((satisfactionCandidates first env).sat.withSelector trueElement).select
        ((satisfactionCandidates second env).sat.withSelector
          falseElement)).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_or_i
    (first second : CoreFragment) (env : SatEnv) :
    dissatisfy (.or_i first second) env =
      (((satisfactionCandidates first env).dsat.withSelector trueElement).select
        ((satisfactionCandidates second env).dsat.withSelector
          falseElement)).usableWitness? := by
  rfl

/-- `andor` selects Y after a satisfying X and Z after a dissatisfying X. Its
    alternate `sat(X) dsat(Y)` dissatisfaction is valid but non-canonical; it is
    not an overcomplete row and therefore keeps its inherited usability. -/
@[simp] theorem satisfactionCandidates_andor
    (first second third : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.andor first second third) env = {
      sat := ((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).sat)
      dsat := ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).dsat).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markNonCanonical) } := by
  rfl

@[simp] theorem satisfactionCandidates_andor_sat
    (first second third : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.andor first second third) env).sat =
      ((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).sat) := by
  rfl

@[simp] theorem satisfactionCandidates_andor_dsat
    (first second third : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.andor first second third) env).dsat =
      ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).dsat).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markNonCanonical) := by
  rfl

@[simp] theorem satisfy_andor
    (first second third : CoreFragment) (env : SatEnv) :
    satisfy (.andor first second third) env =
      (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).select
        ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).sat)).usableWitness? := by
  rfl

@[simp] theorem dissatisfy_andor
    (first second third : CoreFragment) (env : SatEnv) :
    dissatisfy (.andor first second third) env =
      (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates third env).dsat).select
        (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markNonCanonical)).usableWitness? := by
  rfl

@[simp] theorem satisfactionCandidates_c (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.c fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_c (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.c fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_c (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.c fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `a` changes execution stack placement, not candidate metadata or
    serialized witness order. -/
@[simp] theorem satisfactionCandidates_a
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.a fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_a (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.a fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_a (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.a fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `s` also preserves the candidate pair. Its singleton-argument
    typing requirement is enforced by semantic proofs rather than this raw-AST
    candidate function. -/
@[simp] theorem satisfactionCandidates_s
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.s fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_s (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.s fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_s (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.s fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `v` preserves the child's satisfaction candidate and removes its
    dissatisfaction candidate. -/
@[simp] theorem satisfactionCandidates_v
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.v fragment) env =
      { sat := (satisfactionCandidates fragment env).sat } := by
  rfl

@[simp] theorem satisfy_v (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.v fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_v (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.v fragment) env = none := by
  rfl

/-- Wrapper `n` preserves candidates; its opcode-level proof separately
    requires the child's exact Script-number result. -/
@[simp] theorem satisfactionCandidates_n
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.n fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_n (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.n fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_n (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.n fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `d` appends its canonical true branch selector to every possible
    child satisfaction and has one canonical false dissatisfaction. -/
@[simp] theorem satisfactionCandidates_d
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.d fragment) env =
      { sat := (satisfactionCandidates fragment env).sat.withSelector trueElement
        dsat := .usable [falseElement] false } := by
  rfl

@[simp] theorem satisfactionCandidates_d_sat
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.d fragment) env).sat =
      (satisfactionCandidates fragment env).sat.withSelector trueElement := by
  rfl

@[simp] theorem satisfactionCandidates_d_dsat
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.d fragment) env).dsat =
      .usable [falseElement] false := by
  rfl

@[simp] theorem satisfy_d (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.d fragment) env =
      (satisfy fragment env).map (Witness.withSelector · trueElement) := by
  cases selected : (satisfactionCandidates fragment env).sat with
  | impossible =>
      simp [satisfy, selected, CandidateResult.withSelector,
        CandidateResult.usableWitness?]
  | candidate value =>
      cases value with
      | mk witness hasSig status origin =>
          cases status <;>
            simp [satisfy, selected, CandidateResult.withSelector,
              CandidateResult.usableWitness?, SatisfactionCandidate.withSelector]

@[simp] theorem dissatisfy_d (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.d fragment) env = some [falseElement] := by
  rfl

/-- Wrapper `j` preserves child satisfaction. Its canonical empty
    dissatisfaction competes with the non-canonical child dissatisfaction only
    after that child witness is shown to have a nonempty runtime top item. -/
@[simp] theorem satisfactionCandidates_j
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.j fragment) env =
      { sat := (satisfactionCandidates fragment env).sat
        dsat := (CandidateResult.usable [falseElement] false).select
          ((satisfactionCandidates fragment env).dsat
            |>.requireNonemptyRuntimeTop
            |>.markNonCanonical) } := by
  rfl

@[simp] theorem satisfactionCandidates_j_sat
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.j fragment) env).sat =
      (satisfactionCandidates fragment env).sat := by
  rfl

@[simp] theorem satisfactionCandidates_j_dsat
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (.j fragment) env).dsat =
      (CandidateResult.usable [falseElement] false).select
        ((satisfactionCandidates fragment env).dsat
          |>.requireNonemptyRuntimeTop
          |>.markNonCanonical) := by
  rfl

@[simp] theorem satisfy_j (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.j fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_j (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.j fragment) env =
      ((CandidateResult.usable [falseElement] false).select
        ((satisfactionCandidates fragment env).dsat
          |>.requireNonemptyRuntimeTop
          |>.markNonCanonical)).usableWitness? := by
  rfl

/-- Invalid raw threshold arities or arithmetic literals have no satisfaction
    or dissatisfaction. -/
@[simp] theorem satisfactionCandidates_thresh_invalid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    satisfactionCandidates (.thresh threshold fragments) env = {} := by
  simp [satisfactionCandidates, invalid]

/-- A valid raw threshold uses the shared exact-count table for satisfaction
    and the canonical/overcomplete count selection for dissatisfaction. -/
@[simp] theorem satisfactionCandidates_thresh_valid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (valid : candidateThresholdValid threshold fragments.length) :
    satisfactionCandidates (.thresh threshold fragments) env =
      let children := fragments.map (fun fragment =>
        satisfactionCandidates fragment env)
      let states := CandidatePair.countCandidates children
      { sat := CandidatePair.selectExactly threshold children
        dsat := CandidatePair.thresholdDissatisfaction threshold states } := by
  simp [satisfactionCandidates, valid]

@[simp] theorem satisfactionCandidates_thresh_sat
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (valid : candidateThresholdValid threshold fragments.length) :
    (satisfactionCandidates (.thresh threshold fragments) env).sat =
      CandidatePair.selectExactly threshold
        (fragments.map (fun fragment => satisfactionCandidates fragment env)) := by
  rw [satisfactionCandidates_thresh_valid threshold fragments env valid]

@[simp] theorem satisfactionCandidates_thresh_dsat
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (valid : candidateThresholdValid threshold fragments.length) :
    (satisfactionCandidates (.thresh threshold fragments) env).dsat =
      CandidatePair.thresholdDissatisfaction threshold
        (CandidatePair.countCandidates
          (fragments.map (fun fragment =>
            satisfactionCandidates fragment env))) := by
  rw [satisfactionCandidates_thresh_valid threshold fragments env valid]

@[simp] theorem satisfy_thresh_invalid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    satisfy (.thresh threshold fragments) env = none := by
  simp [satisfy, invalid]

@[simp] theorem dissatisfy_thresh_invalid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    dissatisfy (.thresh threshold fragments) env = none := by
  simp [dissatisfy, invalid]

@[simp] theorem satisfy_thresh_valid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (valid : candidateThresholdValid threshold fragments.length) :
    satisfy (.thresh threshold fragments) env =
      (CandidatePair.selectExactly threshold
        (fragments.map (fun fragment =>
          satisfactionCandidates fragment env))).usableWitness? := by
  unfold satisfy
  rw [satisfactionCandidates_thresh_sat threshold fragments env valid]

@[simp] theorem dissatisfy_thresh_valid
    (threshold : Nat) (fragments : List CoreFragment) (env : SatEnv)
    (valid : candidateThresholdValid threshold fragments.length) :
    dissatisfy (.thresh threshold fragments) env =
      (CandidatePair.thresholdDissatisfaction threshold
        (CandidatePair.countCandidates
          (fragments.map (fun fragment =>
            satisfactionCandidates fragment env)))).usableWitness? := by
  unfold dissatisfy
  rw [satisfactionCandidates_thresh_dsat threshold fragments env valid]

@[simp] theorem satisfactionCandidates_multi
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    satisfactionCandidates (.multi threshold keys) env =
      legacyMultiCandidates threshold keys env := by
  rfl

@[simp] theorem satisfy_multi
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    satisfy (.multi threshold keys) env =
      (legacyMultiCandidates threshold keys env).sat.usableWitness? := by
  rfl

@[simp] theorem dissatisfy_multi
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    dissatisfy (.multi threshold keys) env =
      (legacyMultiCandidates threshold keys env).dsat.usableWitness? := by
  rfl

@[simp] theorem satisfactionCandidates_multi_a
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    satisfactionCandidates (.multi_a threshold keys) env =
      multiACandidates threshold keys env := by
  rfl

@[simp] theorem satisfy_multi_a
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    satisfy (.multi_a threshold keys) env =
      (multiACandidates threshold keys env).sat.usableWitness? := by
  rfl

@[simp] theorem dissatisfy_multi_a
    (threshold : Nat) (keys : List PubKey) (env : SatEnv) :
    dissatisfy (.multi_a threshold keys) env =
      (multiACandidates threshold keys env).dsat.usableWitness? := by
  rfl

end LeanMiniscript.Miniscript
