import BernsteinObstacle.PhysicalSimplexCoordinates
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped BigOperators ENNReal
open MeasureTheory

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- The local value estimate in the actual `L2` seminorm on the physical
element. The measure and measurability of the element are explicit; finite
volume is needed for a finite bound. No Sobolev membership is claimed. -/
theorem eLpNorm_affineBasisPhysicalSamplingRecovery_error_le {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (M h : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖b i - b j‖ ≤ h)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint b), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint b),
      ∀ z ∈ Set.range (physicalSimplexPoint b),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (μ : Measure E) (hT : MeasurableSet (Set.range (physicalSimplexPoint b))) :
    eLpNorm (fun p => affineBasisPhysicalSamplingRecovery b n hn f p - f p) 2
      (μ.restrict (Set.range (physicalSimplexPoint b))) ≤
      (μ (Set.range (physicalSimplexPoint b))) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal (M * h ^ 2) := by
  have hpoint : ∀ᵐ p ∂μ.restrict (Set.range (physicalSimplexPoint b)),
      ‖affineBasisPhysicalSamplingRecovery b n hn f p - f p‖ ≤ M * h ^ 2 := by
    filter_upwards [ae_restrict_mem hT] with p hp
    obtain ⟨x, rfl⟩ := hp
    simpa [affineBasisPhysicalSamplingRecovery_eq, Real.norm_eq_abs] using
      physicalSamplingRecovery_abs_error_le_of_lipschitz_fderiv b n hn f M h hM hv hf hDf x
  simpa using eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hpoint

/-- The local `L2` seminorm estimate for actual Frechet-derivative error.
Identifying this derivative with the assembled weak gradient is a separate
obligation, not an assumption hidden in this declaration. -/
theorem eLpNorm_fderiv_affineBasisPhysicalSamplingRecovery_error_le {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (M h C : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖b i - b j‖ ≤ h)
    (hshape : h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ C)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint b), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint b),
      ∀ z ∈ Set.range (physicalSimplexPoint b),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (μ : Measure E) (hT : MeasurableSet (Set.range (physicalSimplexPoint b))) :
    eLpNorm (fun p => fderiv ℝ (affineBasisPhysicalSamplingRecovery b n hn f) p - fderiv ℝ f p) 2
      (μ.restrict (Set.range (physicalSimplexPoint b))) ≤
      (μ (Set.range (physicalSimplexPoint b))) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal ((n : ℝ) * M * C * h) := by
  have hpoint : ∀ᵐ p ∂μ.restrict (Set.range (physicalSimplexPoint b)),
      ‖fderiv ℝ (affineBasisPhysicalSamplingRecovery b n hn f) p - fderiv ℝ f p‖ ≤
        (n : ℝ) * M * C * h := by
    filter_upwards [ae_restrict_mem hT] with p hp
    obtain ⟨x, rfl⟩ := hp
    exact norm_fderiv_affineBasisPhysicalSamplingRecovery_error_le_of_shape
      b n hn f M h C hM hv hshape hf hDf x
  simpa using eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hpoint

end

end BernsteinObstacle
