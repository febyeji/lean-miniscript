import LeanMiniscript.Miniscript.Checked
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

/-!
# Satisfaction availability

The concrete satisfier returns no candidate both when a fragment has no
satisfaction path and when the current environment lacks required material.
This module exposes that distinction without changing candidate selection or
witness generation.
-/

/-- Whether a satisfaction is structurally absent, potentially available with
    more material, or represented by a candidate in the current environment. -/
inductive SatisfactionAvailability where
  | no
  | maybe
  | yes
  deriving Repr, DecidableEq, BEq

namespace CoreFragment

mutual
  /-- Bitcoin Core-style structural satisfiability with a caller-supplied
      predicate for key, timelock, hashlock, and multisig atoms. -/
  def isSatisfiableWith
      (atomSatisfiable : CoreFragment → Bool) : CoreFragment → Bool
    | .zero => false
    | .one => true
    | atom@(.pk_k _) | atom@(.pk_h _) |
        atom@(.older _) | atom@(.after _) |
        atom@(.sha256 _) | atom@(.hash256 _) |
        atom@(.ripemd160 _) | atom@(.hash160 _) |
        atom@(.multi _ _) | atom@(.multi_a _ _) => atomSatisfiable atom
    | .andor x y z =>
        (isSatisfiableWith atomSatisfiable x &&
          isSatisfiableWith atomSatisfiable y) ||
        isSatisfiableWith atomSatisfiable z
    | .and_v x y | .and_b x y =>
        isSatisfiableWith atomSatisfiable x &&
          isSatisfiableWith atomSatisfiable y
    | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
        isSatisfiableWith atomSatisfiable x ||
          isSatisfiableWith atomSatisfiable y
    | .a x | .s x | .c x | .d x | .v x | .j x | .n x =>
        isSatisfiableWith atomSatisfiable x
    | .thresh k fragments =>
        decide (k ≤ countSatisfiableWith atomSatisfiable fragments)

  /-- Number of structurally satisfiable threshold children. -/
  def countSatisfiableWith
      (atomSatisfiable : CoreFragment → Bool) : List CoreFragment → Nat
    | [] => 0
    | fragment :: fragments =>
        (if isSatisfiableWith atomSatisfiable fragment then 1 else 0) +
          countSatisfiableWith atomSatisfiable fragments
end

/-- Whether a satisfaction path exists when every atomic condition is assumed
    available. Public callers normally use this through a `CheckedFragment`,
    which supplies the separate context, shape, and typing validity boundary. -/
def structurallySatisfiable (fragment : CoreFragment) : Bool :=
  fragment.isSatisfiableWith fun _ => true

end CoreFragment

namespace CandidateResult

/-- Classify a concrete result using the independently computed structural
    satisfiability of its fragment. Any retained candidate counts as available,
    including DONTUSE and no-HASSIG candidates; those policies remain visible
    through their existing projections. -/
def availability (result : CandidateResult)
    (structurallyPossible : Bool) : SatisfactionAvailability :=
  match result with
  | .candidate _ => .yes
  | .impossible => if structurallyPossible then .maybe else .no

@[simp] theorem availability_eq_yes_iff (result : CandidateResult)
    (structurallyPossible : Bool) :
    result.availability structurallyPossible = .yes ↔
      ∃ candidate, result = .candidate candidate := by
  cases result <;> cases structurallyPossible <;> simp [availability]

@[simp] theorem availability_eq_maybe_iff (result : CandidateResult)
    (structurallyPossible : Bool) :
    result.availability structurallyPossible = .maybe ↔
      result = .impossible ∧ structurallyPossible = true := by
  cases result <;> cases structurallyPossible <;> simp [availability]

@[simp] theorem availability_eq_no_iff (result : CandidateResult)
    (structurallyPossible : Bool) :
    result.availability structurallyPossible = .no ↔
      result = .impossible ∧ structurallyPossible = false := by
  cases result <;> cases structurallyPossible <;> simp [availability]

end CandidateResult

namespace CheckedFragment

/-- Distinguish structural impossibility from material that is absent in the
    current satisfaction environment. This observes raw candidate presence;
    `satisfy` and `satisfyFinal` continue to enforce DONTUSE and HASSIG. -/
def satisfactionAvailability {ctx : ScriptContext}
    (checked : CheckedFragment ctx) (env : SatEnv) : SatisfactionAvailability :=
  let result := (satisfactionCandidates checked.fragment env).sat
  result.availability checked.fragment.structurallySatisfiable

theorem satisfactionAvailability_eq_yes_iff {ctx : ScriptContext}
    (checked : CheckedFragment ctx) (env : SatEnv) :
    checked.satisfactionAvailability env = .yes ↔
      ∃ candidate,
        (satisfactionCandidates checked.fragment env).sat = .candidate candidate := by
  simp [satisfactionAvailability]

theorem satisfactionAvailability_eq_maybe_iff {ctx : ScriptContext}
    (checked : CheckedFragment ctx) (env : SatEnv) :
    checked.satisfactionAvailability env = .maybe ↔
      (satisfactionCandidates checked.fragment env).sat = .impossible ∧
        checked.fragment.structurallySatisfiable = true := by
  simp [satisfactionAvailability]

theorem satisfactionAvailability_eq_no_iff {ctx : ScriptContext}
    (checked : CheckedFragment ctx) (env : SatEnv) :
    checked.satisfactionAvailability env = .no ↔
      (satisfactionCandidates checked.fragment env).sat = .impossible ∧
        checked.fragment.structurallySatisfiable = false := by
  simp [satisfactionAvailability]

end CheckedFragment

end LeanMiniscript.Miniscript
