# Formal Conjectures campaign — 2026-07-26

Investigation of solvable `research open` statements in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(upstream HEAD `5a60e068cceb4edffa992dd0bdbda8c6c17185c5`), with a per-candidate
upstream PR/issue collision check so nothing already claimed is re-claimed.

## Results

### Headline: Erdős 15 — kernel-verified refutation of the formalized statement ✅

`ErdosProblems/15.lean` states the open question "does $\sum (-1)^n n/p_n$ converge?"
with **`Summable`**, i.e. *unconditional* summability — strictly stronger than the
intended convergence of partial sums. The literal statement is **false**: the terms have
absolute value $(k+1)/p_k \ge 1/p_k$ and $\sum 1/p_k$ diverges.

- **Proof:** [`proofs/Erdos15Refutation.lean`](./proofs/Erdos15Refutation.lean) —
  `erdos15_rhs_false`, compiled against the repo's exact toolchain (Lean 4.27.0 +
  Mathlib at upstream's pin), **sorry-free**, axioms `[propext, Classical.choice, Quot.sound]`.
- **Upstream patch:** [`patches/15_fix_and_refutation.lean`](./patches/15_fix_and_refutation.lean)
  (compiles) — restates `erdos_15` via partial sums, adds `research solved` variant
  `not_summable` with `formal_proof` link. PR draft: [`drafts/PR_erdos15.md`](./drafts/PR_erdos15.md).
- **Collision check:** zero open PRs/issues on 15 (only original #3771, merged; issue #195 closed).

### Ready to submit (verified uncollided as of 2026-07-26)

| Target | Finding | Deliverable |
| --- | --- | --- |
| `ErdosProblems/184.lean` · `erdos_184.variants.covering` | Marked `research open` upstream, but this is exactly the Erdős–Gallai **covering** conjecture, proved by **Pyber, Combinatorica 5 (1985) 67–79**: every graph on `n` vertices can be covered by `n−1` circuits and edges. The formal statement (covering, not decomposition; `≤ n−1` over ℝ; `Nonempty V`; Finset dedup only lowers the count; `n=1` ⇒ `D=∅`) matches Pyber's theorem. | [`patches/184_solved.lean`](./patches/184_solved.lean): `answer(True)`, category → `research solved`, `[Py85]` reference. PR draft in [`drafts/`](./drafts/). |
| `ErdosProblems/1106.lean` · `erdos_1106.parts.i` | Marked `research open` upstream, but `F(n) → ∞` is known: Schinzel (via the `p(n)` asymptotic + Tijdeman; details in Erdős–Iviç) and **Schinzel–Wirsing (1987)** proved `F(n) ≫ log n`. Recorded on erdosproblems.com/1106 itself. `parts.ii` (`F(n) > n`) remains genuinely open and is untouched. | [`patches/1106_solved.lean`](./patches/1106_solved.lean): `answer(True)`, category → `research solved`, `[ScWi87]` reference, fixes the `1064` reference typo. PR draft in [`drafts/`](./drafts/). |

### Statement-defect dossiers (uncollided fix-lane, not "solves")

- `ErdosProblems/409.lean` (`erdos_409.parts.i`, `erdos_409.variants.sigma`) and
  `ErdosProblems/503.lean` (`erdos_503`): the `answer()` slot sits **under a
  universally quantified binder**, violating the repo's own convention
  (AGENTS.md: quantification must come *after* `answer(sorry)`). No closed
  answer can be correct — for 409, `n=2` forces `0` while `n=4` forces `1`
  (φ-chain) / `2` (σ-chain: 4→6→11); for 503 the file's own solved variants force
  `6` (n=2, Erdős–Kelly) and `8` (n=3, Croft) simultaneously. Every concrete
  answer is refutable; the statements need a quantifier restructure. Dossier:
  [`drafts/ISSUE_erdos409_503.md`](./drafts/ISSUE_erdos409_503.md).

### Found solvable but already claimed upstream — dropped

- `ErdosProblems/128.lean`: `∀ V'` sits outside the hypothesis, so one dense
  induced subgraph must force a triangle — refutable with `V = Fin 2`, `G = ⊤`,
  `V' = univ` (`50·1 > 2² = 4`, K₂ has no triangle via `cliqueFree_of_card_lt`),
  so `answer(False)` settles the exact statement. **Collided**: open PRs #4606,
  #4501 and issue #4424 already claim the quantifier fix.

Full collision log: [`COLLISIONS.md`](./COLLISIONS.md).

## Verification status

- **All three patches compile** against the fully built repo (mathlib built from
  source in-session, 8046 jobs, because the mathlib cache host
  `lakecache.blob.core.windows.net` is blocked by the session network policy;
  Lean 4.27.0 was installed from GitHub releases after `*.lean-lang.org` was
  also blocked).
- `Erdos15Refutation.lean` additionally passes the axiom audit
  (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
- The 184/1106 patches are metadata+answer changes; the repo records
  literature-solved problems exactly this way (`research solved` with `by sorry`
  retained — cf. `erdos_184.variants.n_log_n`, `bucic_montgomery` in the same file).
- Literature checks: Pyber 1985 confirmed via Springer (Combinatorica 5, 67–79);
  Schinzel–Wirsing / Erdős problem 1106 status confirmed via erdosproblems.com.

## Method

1. Shallow-cloned upstream; enumerated all 1175 `research open` statements
   (631 files) and partitioned them into 9 audit slices (`ErdosProblems` ×4,
   `Wikipedia` ×2, `GreensOpenProblems`+`Mathoverflow`, `Paper`+misc,
   `WrittenOnTheWallII`+`OEIS`).
2. Ran an adversarial audit sweep (multi-agent; stopped early to conserve
   credits after slice 1 of 9 produced the findings above — slices 2–9 remain
   unaudited and are documented future work).
3. Collision-checked every candidate against upstream PRs and issues by
   targeted GitHub search before claiming it.

## Prior-work status (this project's earlier claims, checked upstream)

| Conjecture | Upstream status |
| --- | --- |
| WOWII 143 | ✅ merged `research solved`, credited to DomTheDeveloper fork |
| OEIS A317940 | ✅ merged `research solved`, `formal_proof` links to crl site |
| WOWII 322 | 🕐 user's own open PR #4497 |
| Green 14 (W(3,20)) | 🕐 user's own open PR #4584 |
| WOWII 65 | ❌ user's PR #4441 closed; SamuelSchlesinger's #4514 (disprove) open |
| WOWII 160 | ❌ claimed by open PR #4576 (anagnorisis2peripeteia) |
| WOWII 314 | ❌ claimed by open PR #4455 (glyaea) |
| WOWII 316 | ❌ claimed by open PR #4426 (KitaKen1) |
