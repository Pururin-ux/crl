import BernsteinObstacle.PhysicalSamplingGradient
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The constant part of the genuine barycentric coordinate of an affine basis. -/
def affineBasisCoordinateConstant {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E) :
    Fin (d + 1) → ℝ := fun i => b.coord i 0

/-- The linear part of the genuine barycentric coordinate, made continuous
using finite-dimensionality. -/
def affineBasisCoordinateDerivative {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E) :
    Fin (d + 1) → E →L[ℝ] ℝ := fun i => (b.coord i).linear.toContinuousLinearMap

theorem affineBasisCoordinate_eq {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E)
    (i : Fin (d + 1)) (p : E) :
    affineBasisCoordinateConstant b i + affineBasisCoordinateDerivative b i p = b.coord i p := by
  have h := (b.coord i).map_vadd (0 : E) p
  simpa [affineBasisCoordinateConstant, affineBasisCoordinateDerivative, add_comm] using h.symm

theorem affineBasisCoordinate_sum_eq_one {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (p : E) :
    (∑ i, (affineBasisCoordinateConstant b i + affineBasisCoordinateDerivative b i p)) = 1 := by
  simp_rw [affineBasisCoordinate_eq]
  exact b.sum_coord_apply_eq_one p

theorem affineBasisCoordinate_reconstruct {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (p : E) :
    (∑ i, (affineBasisCoordinateConstant b i + affineBasisCoordinateDerivative b i p) • b i) = p := by
  simp_rw [affineBasisCoordinate_eq]
  exact b.linear_combination_coord_eq_self p

/-- Genuine affine-basis coordinates recover every barycentric point of the
physical simplex, including its boundary. -/
theorem affineBasisCoordinate_physicalSimplexPoint {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (x : BarycentricPoint d) (i : Fin (d + 1)) :
    affineBasisCoordinateConstant b i +
      affineBasisCoordinateDerivative b i (physicalSimplexPoint b x) = x.1 i := by
  rw [affineBasisCoordinate_eq]
  have hcomb : Finset.univ.affineCombination ℝ b x.1 = physicalSimplexPoint b x := by
    rw [Finset.univ.affineCombination_eq_linear_combination b x.1 x.2.2]
    rfl
  rw [← hcomb]
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) x.2.2

/-- The original positive sampler as a function on a physical affine-basis
element, with all coordinate maps constructed rather than postulated. -/
def affineBasisPhysicalSamplingRecovery {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) (f : E → ℝ) : E → ℝ :=
  affinePhysicalSamplingRecovery b n hn
    (affineBasisCoordinateConstant b) (affineBasisCoordinateDerivative b) f

theorem affineBasisPhysicalSamplingRecovery_eq {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (x : BarycentricPoint d) :
    affineBasisPhysicalSamplingRecovery b n hn f (physicalSimplexPoint b x) =
      physicalSamplingRecovery b n hn f x := by
  exact affinePhysicalSamplingRecovery_eq b n hn
    (affineBasisCoordinateConstant b) (affineBasisCoordinateDerivative b) f
    (physicalSimplexPoint b x) x (affineBasisCoordinate_physicalSimplexPoint b x)

/-- The physical first-order derivative estimate for an actual nondegenerate
affine-basis element, under an explicit coordinate shape bound. -/
theorem norm_fderiv_affineBasisPhysicalSamplingRecovery_error_le_of_shape {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (M h C : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i j, ‖b i - b j‖ ≤ h)
    (hshape : h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ C)
    (hf : ∀ z ∈ Set.range (physicalSimplexPoint b), DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ Set.range (physicalSimplexPoint b),
      ∀ z ∈ Set.range (physicalSimplexPoint b),
        ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖)
    (x : BarycentricPoint d) :
    ‖fderiv ℝ (affineBasisPhysicalSamplingRecovery b n hn f) (physicalSimplexPoint b x) -
      fderiv ℝ f (physicalSimplexPoint b x)‖ ≤ (n : ℝ) * M * C * h := by
  exact norm_fderiv_affinePhysicalSamplingRecovery_error_le_of_shape b n hn
    (affineBasisCoordinateConstant b) (affineBasisCoordinateDerivative b)
    (affineBasisCoordinate_sum_eq_one b) (affineBasisCoordinate_reconstruct b)
    f M h C hM hv hshape hf hDf (physicalSimplexPoint b x) x
    (affineBasisCoordinate_physicalSimplexPoint b x)

end

end BernsteinObstacle
