/-
Kernel-verified refutation of the literal statement of `erdos_15` in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/15.lean,
upstream HEAD 5a60e06, 2026-07-26).

Compiled with the repo's exact toolchain (leanprover/lean4:v4.27.0 + pinned Mathlib):
no errors, no sorry; `#print axioms erdos15_rhs_false` =
[propext, Classical.choice, Quot.sound].

The formalization states the (open) Erdős problem 15 with `Summable`, which is
unconditional summability and implies absolute convergence — but the terms have
absolute value (k+1)/p_k ≥ 1/p_k and ∑ 1/p_k diverges. The intended question
(convergence of partial sums) remains open and is NOT claimed here.
-/
import Mathlib

open Filter

-- The exact RHS of `erdos_15` in FormalConjectures/ErdosProblems/15.lean is
-- `Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime))`.
-- We show it is FALSE, i.e. the correct answer is `answer(False)`,
-- because `Summable` means unconditional (= absolute) convergence,
-- and ∑ (k+1)/p_k ≥ ∑ 1/p_k diverges (Euler).

theorem erdos15_rhs_false :
    ¬ Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) := by
  intro h
  -- Push the summability along the continuous ring hom ℚ → ℝ.
  have hR : Summable (fun k : ℕ =>
      ((((-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime) : ℚ)) : ℝ)) :=
    h.map (Rat.castHom ℝ) Rat.continuous_coe_real
  -- Summable implies absolutely summable in ℝ.
  have habs := hR.abs
  -- The absolute value of the k-th term is (k+1)/p_k ≥ 1/p_k.
  have h1 : Summable (fun k : ℕ => (1 : ℝ) / (Nat.nth Nat.Prime k)) := by
    refine habs.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    have hp : (0 : ℝ) < (Nat.nth Nat.Prime k : ℝ) := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k).pos
    push_cast
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast, abs_of_pos (by positivity : (0:ℝ) < (k : ℝ) + 1)]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_le_div_of_nonneg_right hk1 hp.le
  -- Convert to a sum over the primes via the enumeration `Nat.nth Nat.Prime`.
  have h2 : Summable ({p : ℕ | p.Prime}.indicator fun n => 1 / (n : ℝ)) := by
    have hinj := Nat.nth_injective Nat.infinite_setOf_prime
    have hrange := Nat.range_nth_of_infinite (p := Nat.Prime) Nat.infinite_setOf_prime
    refine (Function.Injective.summable_iff hinj ?_).mp ?_
    · intro x hx
      have : ¬ x.Prime := by
        intro hxp
        exact hx (by rw [hrange]; exact hxp)
      simp [Set.indicator_of_notMem, this]
    · refine h1.congr fun k => ?_
      have hk : (Nat.nth Nat.Prime k).Prime :=
        Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
      simp [Function.comp, Set.indicator_of_mem, hk]
  exact not_summable_one_div_on_primes h2
