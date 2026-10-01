import BernsteinObstacle.PhysicalSimplexRecovery
import Mathlib.Analysis.Calculus.MeanValue

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical simplex is the convex image of the complete barycentric simplex.
This also holds for a degenerate vertex family. -/
theorem convex_range_physicalSimplexPoint {d : ℕ} (v : Fin (d + 1) → E) :
    Convex ℝ (Set.range (physicalSimplexPoint v)) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨y, rfl⟩ := hq
  let z : BarycentricPoint d := ⟨fun i => a * x.1 i + b * y.1 i,
    fun i => add_nonneg (mul_nonneg ha (x.2.1 i)) (mul_nonneg hb (y.2.1 i)), by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        x.2.2, y.2.2, mul_one, mul_one]
      exact hab⟩
  refine ⟨z, ?_⟩
  dsimp [physicalSimplexPoint, z]
  simp_rw [add_smul, mul_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]

/-- Actual Frechet derivatives with a Lipschitz bound yield a quadratic Taylor
remainder. The constant is M, not the sharper M/2. -/
theorem norm_taylor_remainder_le_of_lipschitz_fderiv
    {s : Set E} {f : E → ℝ} {M : ℝ} (hs : Convex ℝ s) (hM : 0 ≤ M)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z)
    (hDf : ∀ p ∈ s, ∀ q ∈ s,
      ‖fderiv ℝ f p - fderiv ℝ f q‖ ≤ M * ‖p - q‖)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  let t := s ∩ Metric.closedBall x ‖y - x‖
  have hxt : x ∈ t := ⟨hx, by simp⟩
  have hyt : y ∈ t := ⟨hy, by simp [Metric.mem_closedBall, dist_eq_norm]⟩
  have hbound : ∀ z ∈ t, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * ‖y - x‖ := by
    intro z hz
    exact (hDf z hz.1 x hx).trans
      (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.2) hM)
  have ht : Convex ℝ t := hs.inter (convex_closedBall x ‖y - x‖)
  have h := ht.norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z hz.1) hbound hxt hyt
  simpa only [pow_two, mul_assoc] using h

/-- Second-order physical C0 recovery error from actual differentiability and
Lipschitz continuity of the Frechet derivative on this physical element.
No inverse map or shape condition is needed; this is not an H1 theorem. -/
theorem physicalSamplingRecovery_abs_error_le_of_lipschitz_fderiv {d : ℕ}
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n) (f : E → ℝ) (M h : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint v), DifferentiableAt ℝ f z)
    (hDf : ∀ p ∈ Set.range (physicalSimplexPoint v),
      ∀ q ∈ Set.range (physicalSimplexPoint v),
        ‖fderiv ℝ f p - fderiv ℝ f q‖ ≤ M * ‖p - q‖)
    (x : BarycentricPoint d) :
    |physicalSamplingRecovery v n hn f x - f (physicalSimplexPoint v x)| ≤ M * h ^ 2 := by
  apply physicalSamplingRecovery_taylor_error_le v n hn f x
    (fderiv ℝ f (physicalSimplexPoint v x)).toLinearMap M h hM hv
  intro y
  simpa [sub_add_eq_sub_sub, Real.norm_eq_abs] using
    norm_taylor_remainder_le_of_lipschitz_fderiv
      (convex_range_physicalSimplexPoint v) hM hf hDf
      (Set.mem_range_self x) (Set.mem_range_self y)

end

end BernsteinObstacle
