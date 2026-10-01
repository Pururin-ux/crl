import BernsteinObstacle.PhysicalFieldDerivative

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The existing sampler evaluated as a genuine function on physical space,
using explicit affine coordinate maps. -/
def affinePhysicalSamplingRecovery {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (a : Fin (d + 1) → ℝ)
    (ℓ : Fin (d + 1) → E →L[ℝ] ℝ) (f : E → ℝ) : E → ℝ :=
  affineSimplexField d n a ℓ
    (fun α => f (physicalSimplexPoint v (simplexLatticePoint d n hn α)))

theorem affinePhysicalSamplingRecovery_eq {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (a : Fin (d + 1) → ℝ)
    (ℓ : Fin (d + 1) → E →L[ℝ] ℝ) (f : E → ℝ)
    (p : E) (x : BarycentricPoint d) (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    affinePhysicalSamplingRecovery v n hn a ℓ f p = physicalSamplingRecovery v n hn f x := by
  exact affineSimplexField_eq_simplexField d n a ℓ _ p x hcoords

/-- Affine reproduction holds as an equality of functions on physical space
provided the coordinate maps really reconstruct every physical point. -/
theorem affinePhysicalSamplingRecovery_affine {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (a : Fin (d + 1) → ℝ)
    (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (hsum : ∀ p : E, ∑ i, (a i + ℓ i p) = 1)
    (hrec : ∀ p : E, ∑ i, (a i + ℓ i p) • v i = p)
    (b : ℝ) (L : E →L[ℝ] ℝ) (p : E) :
    affinePhysicalSamplingRecovery v n hn a ℓ (fun y => b + L y) p = b + L p := by
  have hcoeff :
      (fun α : MultiIndex d n => b + L (physicalSimplexPoint v
        (simplexLatticePoint d n hn α))) =
      (fun α : MultiIndex d n => b + ∑ i, ((α.1 i : ℝ) / (n : ℝ)) * L (v i)) := by
    funext α
    simp [physicalSimplexPoint, simplexLatticePoint, map_sum, map_smul, smul_eq_mul]
  unfold affinePhysicalSamplingRecovery
  rw [hcoeff, affineSimplexField_affineCoefficients d n hn a ℓ hsum]
  have hL := congrArg L (hrec p)
  simpa [map_sum, map_smul, smul_eq_mul] using congrArg (fun z : ℝ => b + z) hL

/-- A local Taylor bound and actual affine-coordinate derivatives give the
physical sampler derivative estimate before shape scaling. No weak derivative,
finite-element assembly, or density theorem is assumed in this statement. -/
theorem norm_fderiv_affinePhysicalSamplingRecovery_error_le {d : ℕ}
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (hsum : ∀ y : E, ∑ i, (a i + ℓ i y) = 1)
    (hrec : ∀ y : E, ∑ i, (a i + ℓ i y) • v i = y)
    (f : E → ℝ) (M h : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint v), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint v),
      ∀ z ∈ Set.range (physicalSimplexPoint v),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (p : E) (x : BarycentricPoint d) (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    ‖fderiv ℝ (affinePhysicalSamplingRecovery v n hn a ℓ f) p - fderiv ℝ f p‖ ≤
      (M * h ^ 2) * ((n : ℝ) * ∑ i, ‖ℓ i‖) := by
  have hh : 0 ≤ h := le_trans (norm_nonneg _) (hv 0 0)
  have hp : physicalSimplexPoint v x = p := by
    simpa [physicalSimplexPoint, hcoords] using hrec p
  have hpin : p ∈ Set.range (physicalSimplexPoint v) := ⟨x, hp⟩
  let q : E → ℝ := fun y => (f p - fderiv ℝ f p p) + fderiv ℝ f p y
  have hq : affinePhysicalSamplingRecovery v n hn a ℓ q = q := by
    funext y
    exact affinePhysicalSamplingRecovery_affine v n hn a ℓ hsum hrec
      (f p - fderiv ℝ f p p) (fderiv ℝ f p) y
  have hqD : fderiv ℝ (affinePhysicalSamplingRecovery v n hn a ℓ q) p = fderiv ℝ f p := by
    rw [hq]
    exact ((fderiv ℝ f p).hasFDerivAt.const_add (f p - fderiv ℝ f p p)).fderiv
  have hclose (y : BarycentricPoint d) :
      |f (physicalSimplexPoint v y) - q (physicalSimplexPoint v y)| ≤ M * h ^ 2 := by
    have hdist : ‖physicalSimplexPoint v y - p‖ ≤ h := by
      rw [← hp]
      exact physicalSimplexPoint_diameter_le v h hv y x
    have ht := norm_taylor_remainder_le_of_lipschitz_fderiv
      (convex_range_physicalSimplexPoint v) hM hf hDf hpin
      (show physicalSimplexPoint v y ∈ Set.range (physicalSimplexPoint v) from ⟨y, rfl⟩)
    have heq : f (physicalSimplexPoint v y) - q (physicalSimplexPoint v y) =
        f (physicalSimplexPoint v y) - f p - fderiv ℝ f p (physicalSimplexPoint v y - p) := by
      simp only [q, map_sub]
      ring
    rw [heq, ← Real.norm_eq_abs]
    exact ht.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) hh |>.2 hdist) hM)
  have hbound := norm_fderiv_affineSimplexField_sub_le d n a ℓ
    (fun α => f (physicalSimplexPoint v (simplexLatticePoint d n hn α)))
    (fun α => q (physicalSimplexPoint v (simplexLatticePoint d n hn α)))
    p x hcoords (M * h ^ 2) (mul_nonneg hM (sq_nonneg h))
    (fun α => hclose (simplexLatticePoint d n hn α))
  change ‖fderiv ℝ (affinePhysicalSamplingRecovery v n hn a ℓ f) p -
    fderiv ℝ (affinePhysicalSamplingRecovery v n hn a ℓ q) p‖ ≤ _ at hbound
  rwa [hqD] at hbound

/-- An explicit element shape bound turns the actual derivative estimate into
first-order local recovery. The shape bound is an assumption to be proved for
the chosen mesh, not a hidden approximation hypothesis. -/
theorem norm_fderiv_affinePhysicalSamplingRecovery_error_le_of_shape {d : ℕ}
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (hsum : ∀ y : E, ∑ i, (a i + ℓ i y) = 1)
    (hrec : ∀ y : E, ∑ i, (a i + ℓ i y) • v i = y)
    (f : E → ℝ) (M h C : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (hshape : h * ∑ i, ‖ℓ i‖ ≤ C)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint v), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint v),
      ∀ z ∈ Set.range (physicalSimplexPoint v),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (p : E) (x : BarycentricPoint d) (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    ‖fderiv ℝ (affinePhysicalSamplingRecovery v n hn a ℓ f) p - fderiv ℝ f p‖ ≤
      (n : ℝ) * M * C * h := by
  have hh : 0 ≤ h := le_trans (norm_nonneg _) (hv 0 0)
  refine (norm_fderiv_affinePhysicalSamplingRecovery_error_le v n hn a ℓ hsum hrec
    f M h hM hv hf hDf p x hcoords).trans ?_
  calc
    (M * h ^ 2) * ((n : ℝ) * ∑ i, ‖ℓ i‖) =
        ((n : ℝ) * M * h) * (h * ∑ i, ‖ℓ i‖) := by ring
    _ ≤ ((n : ℝ) * M * h) * C :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = (n : ℝ) * M * C * h := by ring

end

end BernsteinObstacle
