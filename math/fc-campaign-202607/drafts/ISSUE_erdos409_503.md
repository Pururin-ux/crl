# Issue draft — `answer()` under a binder makes 409 (i, sigma) and 503 unanswerable

**Target:** google-deepmind/formal-conjectures. Collision-checked 2026-07-26: existing
409/503 PRs cover termination, scaffolding sorries, and an sSup fix — none address this.

## Body

AGENTS.md requires quantification to happen **after** `answer(sorry)`. Three statements
violate this, and in each case the quantity the answer must equal depends on the bound
variable, so *no* closed answer can make the theorem true:

- `erdos_409.parts.i`: `∀ n > 0, IsLeast {i | (φ · + 1)^[i] n |>.Prime} answer(sorry)` —
  `n = 2` forces `0`, `n = 4` forces `1`.
- `erdos_409.variants.sigma`: same shape — `n = 2` forces `0`, `n = 4` forces `2`
  (4 → 6 → 11).
- `erdos_503`: `∀ n, IsGreatest {…isosceles sets in ℝⁿ…} answer(sorry)` — the file's own
  solved variants force `6` at `n = 2` (Erdős–Kelly) and `8` at `n = 3` (Croft).

For every concrete closed answer the statements are refutable (for 409 by a small
computation; for 503 modulo the in-file solved variants), while the intended questions
ask for the value as a function of the parameter. Suggested fix: restructure so the
answer is a function applied to the parameter, or split into per-parameter statements,
mirroring how the asymptotic variants in 409 are already phrased.
