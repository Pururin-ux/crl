import BernsteinObstacle.SimplexFinitePartition
import BernsteinObstacle.SimplexAffineReproduction

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
First moments for the actual bounded-index Bernstein sampling operator.
The natural-index moment is already proved upstream. This module transports
that result to the bounded MultiIndex field used by simplexSamplingRecovery.
-/

theorem simplexMultiIndex_sum_eq_piAntidiag {R : Type*} [AddCommMonoid R]
    (d n : ℕ) (F : (Fin (d + 1) → ℕ) → R) :
    (∑ α : MultiIndex d n, F (fun i => (α.1 i : ℕ))) =
      ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n, F α := by
  classical
  refine Finset.sum_bij
    (fun α (_ : α ∈ (Finset.univ : Finset (MultiIndex d n))) =>
      fun i => (α.1 i : ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    exact Finset.mem_piAntidiag.mpr ⟨α.2, fun i _ => Finset.mem_univ i⟩
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
          Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i)
        _ = n := hsum
    let α : MultiIndex d n :=
      ⟨fun i => ⟨β i, Nat.lt_succ_iff.mpr (hbound i)⟩, by simpa using hsum⟩
    exact ⟨α, Finset.mem_univ _, rfl⟩
  · intro α hα
    rfl

theorem simplexBasis_first_moment (d n : ℕ) (j : Fin (d + 1))
    (x : BarycentricPoint d) :
    (∑ α : MultiIndex d n, (α.1 j : ℝ) * simplexBasis d n α x) =
      (n : ℝ) * x.1 j := by
  simp_rw [simplexBasis_eq_simplexBasisNat]
  exact (simplexMultiIndex_sum_eq_piAntidiag d n
    (fun α => (α j : ℝ) * simplexBasisNat d n α x)).trans
      (simplexBasisNat_firstMoment_unnormalized d n j x)

theorem simplexSamplingRecovery_coordinate (d n : ℕ) (hn : 0 < n)
    (j : Fin (d + 1)) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn (fun y => y.1 j) x = x.1 j := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp only [simplexSamplingRecovery, simplexSamplingCoefficients,
    simplexField, simplexLatticePoint_apply, div_mul_eq_mul_div,
    ← Finset.sum_div, simplexBasis_first_moment]
  exact mul_div_cancel_left₀ (x.1 j) hnR

theorem simplexSamplingRecovery_affine (d n : ℕ) (hn : 0 < n)
    (a : ℝ) (b : Fin (d + 1) → ℝ) (x : BarycentricPoint d) :
    simplexSamplingRecovery d n hn (fun y => a + ∑ i, b i * y.1 i) x =
      a + ∑ i, b i * x.1 i := by
  unfold simplexSamplingRecovery simplexSamplingCoefficients simplexField
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [← Finset.mul_sum, simplexBasis_sum_eq_one, mul_one, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  exact simplexSamplingRecovery_coordinate d n hn i x

end

end BernsteinObstacle
