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
- For non-trivial changes, include a concise commit body when useful.
- Keep rationale and tradeoffs in the user-facing explanation, not in the
  commit body.

## Boundaries

- Changes land through pull requests against `main`.
- `lean-toolchain`, `lake-manifest.json`, the `lean_hash160` revision in
  `lakefile.lean`, and the Bitcoin Core revision pinned in
  `.github/workflows/ci.yml` change only when the task asks for it.
- Regenerate fixtures only through the `scripts/generate_*` generators, and
  name the generator and pinned source in the commit body.
- `AI_USAGE.md` sets the verification rules for AI-written proofs; follow it.
