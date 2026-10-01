import BernsteinObstacle.PhysicalSimplexLpEstimate
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped BigOperators ENNReal
open MeasureTheory

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The classical gradient-error norm is exactly the operator-norm error of
the actual Frechet derivatives, by the Riesz isometry. -/
theorem norm_gradient_sub_eq_norm_fderiv_sub (f g : E → ℝ) (p : E) :
    ‖gradient f p - gradient g p‖ = ‖fderiv ℝ f p - fderiv ℝ g p‖ := by
  rw [gradient, gradient, ← map_sub]
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

theorem eLpNorm_gradient_sub_eq_eLpNorm_fderiv_sub [MeasurableSpace E]
    (f g : E → ℝ) (q : ℝ≥0∞) (μ : Measure E) :
    eLpNorm (fun p => gradient f p - gradient g p) q μ =
      eLpNorm (fun p => fderiv ℝ f p - fderiv ℝ g p) q μ := by
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall (fun p => norm_gradient_sub_eq_norm_fderiv_sub f g p)

variable [FiniteDimensional ℝ E]

/-- First-order error for the actual classical gradient on a physical element.
The global assembled weak-gradient identity is still a separate obligation. -/
theorem norm_gradient_affineBasisPhysicalSamplingRecovery_error_le_of_shape {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (M h C : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖b i - b j‖ ≤ h)
    (hshape : h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ C)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint b), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint b),
      ∀ z ∈ Set.range (physicalSimplexPoint b),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (x : BarycentricPoint d) :
    ‖gradient (affineBasisPhysicalSamplingRecovery b n hn f) (physicalSimplexPoint b x) -
      gradient f (physicalSimplexPoint b x)‖ ≤ (n : ℝ) * M * C * h := by
  rw [norm_gradient_sub_eq_norm_fderiv_sub]
  exact norm_fderiv_affineBasisPhysicalSamplingRecovery_error_le_of_shape
    b n hn f M h C hM hv hshape hf hDf x

theorem eLpNorm_gradient_affineBasisPhysicalSamplingRecovery_error_le
    [MeasurableSpace E] {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (M h C : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖b i - b j‖ ≤ h)
    (hshape : h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ C)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint b), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint b),
      ∀ z ∈ Set.range (physicalSimplexPoint b),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (μ : Measure E) (hT : MeasurableSet (Set.range (physicalSimplexPoint b))) :
    eLpNorm (fun p => gradient (affineBasisPhysicalSamplingRecovery b n hn f) p - gradient f p) 2
      (μ.restrict (Set.range (physicalSimplexPoint b))) ≤
      (μ (Set.range (physicalSimplexPoint b))) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal ((n : ℝ) * M * C * h) := by
  rw [eLpNorm_gradient_sub_eq_eLpNorm_fderiv_sub]
  exact eLpNorm_fderiv_affineBasisPhysicalSamplingRecovery_error_le
    b n hn f M h C hM hv hshape hf hDf μ hT

end

end BernsteinObstacle
