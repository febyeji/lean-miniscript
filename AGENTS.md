# Repository Instructions

## Lean Work

- Run `lake build` after changing Lean code.
- Keep proof claims aligned with what the Lean files actually prove.
- If a change leaves `sorry`, `admit`, or a new axiom in place, mention the
  exact scope and reason in the commit body or PR body.
- Prefer recording unfinished theorem work in comments with a `TODO(...)`
  prefix when a declaration does not need to exist yet.

## Commits

- Use conventional commit format:
  `<type>(<scope>): <imperative verb> <what changed>`.
- Allowed types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`,
  `style`.
- For non-trivial changes, include a body with `WHAT changed` bullets.
- Keep rationale and tradeoffs in the user-facing explanation, not in the
  commit body.
