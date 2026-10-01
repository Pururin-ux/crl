import BernsteinObstacle.PhysicalWeakDerivative
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open scoped NNReal ENNReal
open MeasureTheory Filter Set Topology

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def shrinkingDifferenceStep (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem shrinkingDifferenceStep_pos (n : ℕ) : 0 < shrinkingDifferenceStep n := by
  unfold shrinkingDifferenceStep
  positivity

theorem tendsto_shrinkingDifferenceStep :
    Tendsto shrinkingDifferenceStep atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))), ?_⟩
  exact Eventually.of_forall shrinkingDifferenceStep_pos

def physicalDifferenceQuotient (f : E → ℝ) (v : E) (t : ℝ) (p : E) : ℝ :=
  t⁻¹ * (f (p + t • v) - f p)

/-- Lipschitz control gives a uniform bound for the actual difference quotient,
independent of its positive step size. -/
theorem norm_physicalDifferenceQuotient_le {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (v : E) {t : ℝ} (ht : 0 < t) (p : E) :
    ‖physicalDifferenceQuotient f v t p‖ ≤ C * ‖v‖ := by
  have hbound := hf.dist_le_mul (p + t • v) p
  simp only [dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht] at hbound
  calc
    ‖physicalDifferenceQuotient f v t p‖ = t⁻¹ * ‖f (p + t • v) - f p‖ := by
      rw [physicalDifferenceQuotient, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    _ ≤ t⁻¹ * (C * (t * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht.le)
    _ = C * ‖v‖ := by field_simp <;> ring

theorem tendsto_physicalDifferenceQuotient {f : E → ℝ} {p : E} {v : E} {L : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f L p) :
    Tendsto (fun n => physicalDifferenceQuotient f v (shrinkingDifferenceStep n) p)
      atTop (𝓝 (L v)) := by
  simpa only [physicalDifferenceQuotient, smul_eq_mul, Function.comp_def] using!
    (hf.hasLineDerivAt v).tendsto_slope_zero_right.comp tendsto_shrinkingDifferenceStep

/-- Rademacher and dominated convergence identify the integral limit of the
actual difference quotients paired with a continuous compactly supported test.
This is not yet the integration-by-parts identity. -/
theorem tendsto_integral_physicalDifferenceQuotient_mul {f φ : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hφ : Continuous φ) (hcompact : HasCompactSupport φ) (v : E) :
    Tendsto (fun n => ∫ p, physicalDifferenceQuotient f v (shrinkingDifferenceStep n) p * φ p)
      atTop (𝓝 (∫ p, (fderiv ℝ f p) v * φ p)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => (C * ‖v‖) * ‖φ p‖)
  · intro n
    have hcont : Continuous (fun p => physicalDifferenceQuotient f v (shrinkingDifferenceStep n) p * φ p) := by
      unfold physicalDifferenceQuotient
      exact (continuous_const.mul
        ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)).mul hφ
    exact hcont.aestronglyMeasurable
  · exact (hφ.integrable_of_hasCompactSupport hcompact).norm.const_mul _
  · intro n
    exact ae_of_all _ fun p => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_physicalDifferenceQuotient_le hf v (shrinkingDifferenceStep_pos n) p) (norm_nonneg _)
  · filter_upwards [hf.ae_differentiableAt (μ := volume)] with p hp
    exact (tendsto_physicalDifferenceQuotient hp.hasFDerivAt).mul_const (φ p)

/-- A genuine C1 compactly supported scalar function has a finite global
Lipschitz constant, constructed from its actual continuous derivative. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hsupport : HasCompactSupport (fderiv ℝ f) := hcompact.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hsupport.exists_bound_of_continuousOn hDf.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) ?_⟩
  intro p
  by_cases hp : p ∈ tsupport (fderiv ℝ f)
  · exact_mod_cast (hC p hp).trans (le_max_left C 0)
  · rw [image_eq_zero_of_notMem_tsupport hp, nnnorm_zero]
    exact zero_le

/-- The actual derivative components of a compactly supported Lipschitz
function belong to Lp. No weak derivative is assumed in this statement. -/
theorem memLp_fderiv_apply_of_lipschitz_hasCompactSupport {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hcompact : HasCompactSupport f) (q : ℝ≥0∞) (v : E) :
    MemLp (fun p => (fderiv ℝ f p) v) q volume := by
  apply (hcompact.fderiv_apply (𝕜 := ℝ) v).memLp_of_bound
    (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable (C * ‖v‖)
  exact ae_of_all _ fun p =>
    ((fderiv ℝ f p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

end

end BernsteinObstacle
