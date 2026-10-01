import BernsteinObstacle.SimplexPartition
import BernsteinObstacle.SimplexRecovery

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
The existing partition theorem uses natural-valued antidiagonal indices,
whereas the sampling recovery uses bounded MultiIndex indices. This file
proves the exact bridge, then derives constant reproduction and stability
for the actual recovery field. It does not assert H1 approximation.
-/

theorem simplexBasis_eq_simplexBasisNat (d n : ℕ)
    (α : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis d n α x =
      simplexBasisNat d n (fun i => (α.1 i : ℕ)) x := by
  have hspec := Nat.multinomial_spec
    (Finset.univ : Finset (Fin (d + 1))) (fun i => (α.1 i : ℕ))
  rw [α.2] at hspec
  have hreal :
      (∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ)) *
        (Nat.multinomial Finset.univ (fun i => (α.1 i : ℕ)) : ℝ) =
      (Nat.factorial n : ℝ) := by
    exact_mod_cast hspec
  have hprod :
      (∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ)) ≠ 0 := by
    positivity
  have hcoef :
      (Nat.multinomial Finset.univ (fun i => (α.1 i : ℕ)) : ℝ) =
      (Nat.factorial n : ℝ) /
        ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ) := by
    apply (eq_div_iff hprod).2
    simpa only [mul_comm] using hreal
  unfold simplexBasis simplexBasisNat
  rw [hcoef]

/-- The bounded finite-index basis used by the recovery is a partition of unity. -/
theorem simplexBasis_sum_eq_one (d n : ℕ) (x : BarycentricPoint d) :
    (∑ α : MultiIndex d n, simplexBasis d n α x) = 1 := by
  classical
  rw [← simplexBasisNat_sum_eq_one d n x]
  refine Finset.sum_bij
    (fun α (_ : α ∈ (Finset.univ : Finset (MultiIndex d n))) =>
      fun i => (α.1 i : ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    exact Finset.mem_piAntidiag.mpr
      ⟨α.2, fun i _ => Finset.mem_univ i⟩
  · intro α hα β hβ heq
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun heq i
  · intro β hβ
    have hsum := (Finset.mem_piAntidiag.mp hβ).1
    have hbound : ∀ i, β i ≤ n := by
      intro i
      calc
        β i ≤ ∑ j : Fin (d + 1), β j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (β j))
            (Finset.mem_univ i)
        _ = n := hsum
    let α : MultiIndex d n :=
      ⟨fun i => ⟨β i, Nat.lt_succ_iff.mpr (hbound i)⟩, by simpa using hsum⟩
    refine ⟨α, Finset.mem_univ _, ?_⟩
    funext i
    rfl
  · intro α hα
    exact simplexBasis_eq_simplexBasisNat d n α x

theorem simplexField_const (d n : ℕ) (c : ℝ) (x : BarycentricPoint d) :
    simplexField d n (fun _ => c) x = c := by
  unfold simplexField
  rw [← Finset.mul_sum, simplexBasis_sum_eq_one, mul_one]

theorem simplexField_lower_bound (d n : ℕ)
    (c : MultiIndex d n → ℝ) (m : ℝ) (hc : ∀ α, m ≤ c α)
    (x : BarycentricPoint d) :
    m ≤ simplexField d n c x := by
  calc
    m = ∑ α : MultiIndex d n, m * simplexBasis d n α x := by
      rw [← Finset.mul_sum, simplexBasis_sum_eq_one, mul_one]
    _ ≤ ∑ α : MultiIndex d n, c α * simplexBasis d n α x := by
      exact Finset.sum_le_sum fun α _ =>
        mul_le_mul_of_nonneg_right (hc α) (simplexBasis_nonneg d n α x)
    _ = simplexField d n c x := rfl

theorem simplexField_upper_bound (d n : ℕ)
    (c : MultiIndex d n → ℝ) (M : ℝ) (hc : ∀ α, c α ≤ M)
    (x : BarycentricPoint d) :
    simplexField d n c x ≤ M := by
  calc
    simplexField d n c x =
        ∑ α : MultiIndex d n, c α * simplexBasis d n α x := rfl
    _ ≤ ∑ α : MultiIndex d n, M * simplexBasis d n α x := by
      exact Finset.sum_le_sum fun α _ =>
        mul_le_mul_of_nonneg_right (hc α) (simplexBasis_nonneg d n α x)
    _ = M := by
      rw [← Finset.mul_sum, simplexBasis_sum_eq_one, mul_one]

theorem simplexSamplingRecovery_const (d n : ℕ) (hn : 0 < n)
    (c : ℝ) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn (fun _ => c) x = c := by
  exact simplexField_const d n c x

theorem simplexSamplingRecovery_mem_Icc (d n : ℕ) (hn : 0 < n)
    (w : BarycentricPoint d → ℝ) (m M : ℝ)
    (hw : ∀ y, w y ∈ Set.Icc m M) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn w x ∈ Set.Icc m M := by
  constructor
  · exact simplexField_lower_bound d n (simplexSamplingCoefficients d n hn w) m
      (fun α => (hw (simplexLatticePoint d n hn α)).1) x
  · exact simplexField_upper_bound d n (simplexSamplingCoefficients d n hn w) M
      (fun α => (hw (simplexLatticePoint d n hn α)).2) x

theorem simplexSamplingRecovery_sub (d n : ℕ) (hn : 0 < n)
    (f g : BarycentricPoint d → ℝ) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn (fun y => f y - g y) x =
      simplexSamplingRecovery d n hn f x - simplexSamplingRecovery d n hn g x := by
  simp only [simplexSamplingRecovery, simplexSamplingCoefficients,
    simplexField, sub_mul, Finset.sum_sub_distrib]

/-- Recovery is a contraction for any uniform pointwise difference bound. -/
theorem simplexSamplingRecovery_abs_sub_le (d n : ℕ) (hn : 0 < n)
    (f g : BarycentricPoint d → ℝ) (ε : ℝ)
    (hclose : ∀ y, |f y - g y| ≤ ε) (x : BarycentricPoint d) :
    |simplexSamplingRecovery d n hn f x -
      simplexSamplingRecovery d n hn g x| ≤ ε := by
  have h := simplexSamplingRecovery_mem_Icc d n hn (fun y => f y - g y)
    (-ε) ε (fun y => abs_le.mp (hclose y)) x
  rw [simplexSamplingRecovery_sub] at h
  exact abs_le.mpr h

theorem simplexSamplingRecovery_abs_error_le (d n : ℕ) (hn : 0 < n)
    (f : BarycentricPoint d → ℝ) (x : BarycentricPoint d) (ε : ℝ)
    (hclose : ∀ y, |f y - f x| ≤ ε) :
    |simplexSamplingRecovery d n hn f x - f x| ≤ ε := by
  have h := simplexSamplingRecovery_abs_sub_le d n hn f (fun _ => f x) ε hclose x
  simpa only [simplexSamplingRecovery_const] using h

end

end BernsteinObstacle
