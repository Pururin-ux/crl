# PR draft — fix(ErdosProblems/15): use partial-sum convergence; record refutation of the `Summable` form

**Target:** google-deepmind/formal-conjectures · file `FormalConjectures/ErdosProblems/15.lean`
**Patch:** [`../patches/15_fix_and_refutation.lean`](../patches/15_fix_and_refutation.lean)
**Collision check (2026-07-26):** no open PRs/issues touch `ErdosProblems/15` or `erdos_15` (only #3771, the original formalization, merged Apr 17 2026; its issue #195 closed). Re-verify before submitting.

## Body

[erdosproblems.com/15](https://www.erdosproblems.com/15) asks whether
$\sum_n (-1)^n n/p_n$ **converges** — i.e. whether the sequence of partial sums of this
alternating series converges. The current formalization states the RHS with `Summable`,
which for `ℚ`-valued (or `ℝ`-valued) series is *unconditional* summability and implies
absolute convergence. That is false for elementary reasons unrelated to the open problem:
the terms have absolute value $(k+1)/p_k \ge 1/p_k$, and $\sum 1/p_k$ diverges (Euler).

So the literal statement `erdos_15` is refutable while the intended problem is open.
This PR:

1. restates `erdos_15` as convergence of partial sums
   (`∃ L : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, …) atTop (𝓝 L)`), keeping the
   0-indexing convention of the original;
2. adds `erdos_15.variants.not_summable` (`research solved`) recording that the previous
   `Summable` form is false, with a `formal_proof` link to a complete, sorry-free Lean 4
   proof (axioms: `propext`, `Classical.choice`, `Quot.sound` only):
   [Erdos15Refutation.lean](https://github.com/DomTheDeveloper/crl/blob/claude/deep-mind-formal-conjectures-qih80f/math/fc-campaign-202607/proofs/Erdos15Refutation.lean).

Proof outline of the refutation: `Summable` in `ℚ` maps along the continuous ring hom
`ℚ → ℝ` to `Summable` in `ℝ`; `Summable.abs` gives absolute summability; comparison
(`1/p_k ≤ (k+1)/p_k`) and reindexing along the injective enumeration `Nat.nth Nat.Prime`
yields summability of `{p | p.Prime}.indicator (fun n => 1/n)`, contradicting
mathlib's `not_summable_one_div_on_primes`.

Alternative shape if preferred: resolve the existing statement with `answer(False)` +
category `research solved` instead of restating it; the refutation proof is the same.
