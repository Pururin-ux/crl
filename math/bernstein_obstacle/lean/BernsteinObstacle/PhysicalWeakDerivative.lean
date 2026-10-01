import BernsteinObstacle.PhysicalPolynomialSmooth
import BernsteinObstacle.PhysicalSimplexGradient
import BernsteinObstacle.SobolevH01Port
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Actual classical-to-weak derivative bridge on the pinned project stack

The integration-by-parts argument is adapted from
`DeGiorgi/SobolevSpace/WeakDerivatives.lean`, theorem
`HasWeakPartialDeriv.of_contDiff`, at
`4c1b3077d3782b24065184df4ba59501b2e56fc7` (Apache-2.0).
No DeGiorgi package dependency is introduced. The target weak derivative is
the actual integral-based definition in the project's `SobolevH01Port`.
This local bridge does not assert an assembled piecewise weak gradient.
-/

open scoped BigOperators
open MeasureTheory Set Function

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual global C1 differentiability supplies the project's integral-based
weak partial derivative on any open physical domain. -/
theorem hasWeakPartialDeriv_of_contDiff {Ω : Set E} (_hΩ : IsOpen Ω)
    {i : Fin d} {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    SobolevH01Port.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφ_supp hφ_sub
  let v := EuclideanSpace.single i (1 : ℝ)
  have h_fderiv_supp : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφ_sub
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
      ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      (fun x _ => hf_diff x) (fun x _ => hφ_diff x)
  · intro x hx
    have hnot : x ∉ tsupport φ := fun h => hx (hφ_sub h)
    apply mul_eq_zero.mpr
    right
    by_contra hne
    exact hnot (subset_tsupport φ (mem_support.mpr hne))
  · intro x hx
    have hnot : x ∉ tsupport (fun x => (fderiv ℝ φ x) v) :=
      fun h => hx (h_fderiv_supp h)
    apply mul_eq_zero.mpr
    right
    by_contra hne
    exact hnot (subset_tsupport _ (mem_support.mpr hne))

theorem gradient_component_eq_fderiv_apply (f : E → ℝ) (p : E) (i : Fin d) :
    gradient f p i = (fderiv ℝ f p) (EuclideanSpace.single i 1) := by
  calc
    gradient f p i =
        InnerProductSpace.toDual ℝ E (gradient f p) (EuclideanSpace.single i 1) := by
      rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
      simp
    _ = (fderiv ℝ f p) (EuclideanSpace.single i 1) :=
      congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
        (toDual_gradient (f := f) (x := p))

/-- Actual physical element polynomials have the integral-based weak gradient
given by their classical gradient. Input sampling values need no smoothness. -/
theorem hasWeakGrad_affineBasisPhysicalSamplingRecovery
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) {Ω : Set E} (hΩ : IsOpen Ω) :
    SobolevH01Port.HasWeakGrad (gradient (affineBasisPhysicalSamplingRecovery b n hn f))
      (affineBasisPhysicalSamplingRecovery b n hn f) Ω := by
  intro i
  simp_rw [gradient_component_eq_fderiv_apply]
  exact hasWeakPartialDeriv_of_contDiff hΩ
    (contDiff_affineBasisPhysicalSamplingRecovery 1 b n hn f)

end

end BernsteinObstacle
