import BernsteinObstacle.PhysicalDiscreteCone

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem physicalBernsteinField_linear_coefficients
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (c e : MultiIndex d n → ℝ) (a t : ℝ) (x : E) :
    physicalBernsteinField b n (fun α => a * c α + t * e α) x =
      a * physicalBernsteinField b n c x + t * physicalBernsteinField b n e x := by
  simp only [physicalBernsteinField, affineSimplexField, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

/-- Actual local nonnegative coefficients are stable under nonnegative
linear combinations, and canonical L2 representatives respect those
combinations almost everywhere. Conformity and zero trace remain enforced
by the constructed H01 ambient subspace. -/
theorem convex_physicalBernsteinH01Cone {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) : Convex ℝ (physicalBernsteinH01Cone b n Ω hΩ) := by
  rintro z ⟨c, hc, heqc⟩ w ⟨e, he, heqe⟩ a t ha ht _hat
  refine ⟨fun T α => a * c T α + t * e T α,
    fun T α => add_nonneg (mul_nonneg ha (hc T α)) (mul_nonneg ht (he T α)), ?_⟩
  intro T
  change ∀ᵐ x ∂volume.restrict Ω, x ∈ Set.range (physicalSimplexPoint (b T)) →
    (a • z.1.1 0 + t • w.1.1 0) x =
      physicalBernsteinField (b T) n (fun α => a * c T α + t * e T α) x
  filter_upwards [heqc T, heqe T,
    Lp.coeFn_add (a • z.1.1 0) (t • w.1.1 0),
    Lp.coeFn_smul a (z.1.1 0), Lp.coeFn_smul t (w.1.1 0)] with x hcx hex hadd hca het hx
  rw [hadd, Pi.add_apply, hca, het, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    hcx hx, hex hx, physicalBernsteinField_linear_coefficients]

theorem zero_mem_physicalNonnegativeH01Cone {Ω : Set E} (hΩ : IsOpen Ω) :
    (0 : physicalH01Submodule Ω hΩ) ∈ physicalNonnegativeH01Cone Ω hΩ := by
  change 0 ≤ physicalH01FunctionLp Ω hΩ 0
  simp only [map_zero, le_refl]

end

end BernsteinObstacle
