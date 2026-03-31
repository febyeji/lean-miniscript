# AI Usage Guide

AI may be used to write, review, refactor, and search for Lean code and proofs.
Correctness claims should be based on the checked Lean files and direct review
of theorem statements, not on AI confidence.

## Acceptable Uses

- Writing Lean definitions, comments, and theorem plans.
- Reviewing Lean changes for statement strength, proof gaps, and maintainability.
- Suggesting proof strategies or local proof terms.
- Refactoring module structure while preserving behavior.
- Summarizing external specifications before manually checking them against
  primary sources.

## Verification Rules

- A proof is complete only when `lake build` succeeds and the relevant theorem
  has no `sorry`, `admit`, placeholder axiom, or hidden assumption.
- A compiled theorem is still only as strong as its statement. The theorem
  statement itself should be reviewed directly before claiming a real
  Miniscript property has been proved.
- If `sorry`, `admit`, or a new axiom remains, record its exact scope and reason
  in the commit body or PR body.
- Before publishing or submitting proof claims, check the final diff, run
  `lake build`, and search for unfinished placeholders.

## Commit Hygiene

- Keep AI-assisted changes small enough to review.
- Keep generated proof terms close to the theorem statements they prove.
