import BernsteinObstacle.Core

open scoped BigOperators Polynomial

namespace BernsteinObstacle

/-!
A regression guard for the distinction between positive sampling recovery and
high-order interpolation: the sampler does not reproduce a square at fixed n.
The univariate moment identities are upstream Mathlib results.
-/

theorem curve_square_sampling_error (n : ℕ) (hn : 0 < n) (x : ℝ) :
    curve n (fun k => ((k : ℝ) / (n : ℝ)) ^ 2) x - x ^ 2 =
      x * (1 - x) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hfirst : (∑ k ∈ Finset.range (n + 1), (k : ℝ) * basis n k x) =
      (n : ℝ) * x := by
    have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ n)
    simpa [nsmul_eq_mul, Polynomial.eval_finsetSum] using h
  have hvariance :
      (∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x - k) ^ 2 * basis n k x) =
        (n : ℝ) * x * (1 - x) := by
    have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.variance ℝ n)
    simpa [nsmul_eq_mul, Polynomial.eval_finsetSum] using h
  have hexpand :
      (∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x - k) ^ 2 * basis n k x) =
        (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * basis n k x) -
          (n : ℝ) ^ 2 * x ^ 2 := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          (((n : ℝ) * x) ^ 2 * basis n k x -
            (2 * (n : ℝ) * x) * ((k : ℝ) * basis n k x) +
            (k : ℝ) ^ 2 * basis n k x) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, basis_sum_eq_one, hfirst]
        ring
  have hsecond :
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * basis n k x) =
        (n : ℝ) ^ 2 * x ^ 2 + (n : ℝ) * x * (1 - x) := by
    rw [hexpand] at hvariance
    linarith
  have hcurve : curve n (fun k => ((k : ℝ) / (n : ℝ)) ^ 2) x =
      (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * basis n k x) / (n : ℝ) ^ 2 := by
    simp only [curve, div_pow, div_mul_eq_mul_div, Finset.sum_div]
  rw [hcurve, hsecond]
  field_simp [hnR]
  ring

theorem curve_square_sampling_midpoint_error (n : ℕ) (hn : 0 < n) :
    curve n (fun k => ((k : ℝ) / (n : ℝ)) ^ 2) (1 / 2) - (1 / 2) ^ 2 =
      1 / (4 * (n : ℝ)) := by
  rw [curve_square_sampling_error n hn]
  ring

end BernsteinObstacle
