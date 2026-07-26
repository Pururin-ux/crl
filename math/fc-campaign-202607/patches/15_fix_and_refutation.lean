/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 15: Convergence of Series with Primes

*Reference:* [erdosproblems.com/15](https://www.erdosproblems.com/15)
-/

namespace Erdos15

open Filter Topology

/--
Is it true that $\sum_{n=1}^\infty(-1)^n\frac{n}{p_n}$ converges,
where $p_n$ is the sequence of primes?

Note: In the problem statement, $p_n$ is the $n$-th prime, indexed such that $p_1=2, p_2=3, \ldots$.
We 0-index here to reflect how Nat.nth works.

Convergence here is convergence of the sequence of partial sums, as in the source problem:
the series is alternating and is not absolutely convergent (see
`erdos_15.variants.not_summable`), so the stronger `Summable` (unconditional summability)
is false for elementary reasons and does not capture the intended question.
-/
@[category research open, AMS 11]
theorem erdos_15 : answer(sorry) ↔
    ∃ L : ℝ, Tendsto
      (fun N => ∑ k ∈ Finset.range N, ((-1 : ℝ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)))
      atTop (𝓝 L) := by
  sorry

/--
The series $\sum_{n=1}^\infty(-1)^n\frac{n}{p_n}$ is not unconditionally summable: the
$k$-th term has absolute value $(k+1)/p_k \ge 1/p_k$ and $\sum 1/p_k$ diverges, so
`Summable` (which in $\mathbb{Q}$, mapped into $\mathbb{R}$, implies absolute convergence)
fails. This resolves (negatively) the statement of this problem as it was previously
formalised here; the intended question, convergence of the partial sums, remains open as
`erdos_15`.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/crl/blob/claude/deep-mind-formal-conjectures-qih80f/math/fc-campaign-202607/proofs/Erdos15Refutation.lean"]
theorem erdos_15.variants.not_summable :
    ¬ Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) := by
  sorry

end Erdos15
