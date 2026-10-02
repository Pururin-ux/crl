import BernsteinObstacle.PhysicalC1ChainRule
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  simpa only [deriv_const] using heq.deriv_eq

theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  simpa only [deriv_const] using heq.deriv_eq

theorem exists_bound_weighted_deriv_smoothTransition :
    ∃ B : ℝ≥0, ∀ t : ℝ, ‖t * deriv Real.smoothTransition t‖ ≤ B := by
  have hc : Continuous (fun t : ℝ => t * deriv Real.smoothTransition t) :=
    continuous_id.mul
      ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).continuous_deriv (by simp))
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨⟨max M 0, le_max_right M 0⟩, fun t => ?_⟩
  rcases lt_or_ge t 0 with ht | ht
  · simp only [deriv_smoothTransition_of_neg ht, mul_zero, norm_zero]
    exact le_max_right _ _
  · rcases le_or_gt t 1 with ht1 | ht1
    · exact (hM t ⟨ht, ht1⟩).trans (le_max_left _ _)
    · simp only [deriv_smoothTransition_of_one_lt ht1, mul_zero, norm_zero]
      exact le_max_right _ _

/-- Globally nonnegative C-infinity approximation of the scalar positive
part, with value zero at zero. The derivative bound proved below is uniform
in the smoothing scale, rather than supplied as an analytical assumption. -/
def physicalPositiveRegularizer (δ t : ℝ) : ℝ := t * Real.smoothTransition (t / δ)

@[simp] theorem physicalPositiveRegularizer_zero (δ : ℝ) :
    physicalPositiveRegularizer δ 0 = 0 := by simp [physicalPositiveRegularizer]

theorem contDiff_physicalPositiveRegularizer (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalPositiveRegularizer δ) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ))

theorem physicalPositiveRegularizer_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ physicalPositiveRegularizer δ t := by
  by_cases ht : 0 ≤ t
  · exact mul_nonneg ht (Real.smoothTransition.nonneg _)
  · simp only [physicalPositiveRegularizer,
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hδ.le),
      mul_zero, le_refl]

theorem norm_physicalPositiveRegularizer_le (δ t : ℝ) :
    ‖physicalPositiveRegularizer δ t‖ ≤ ‖t‖ := by
  rw [physicalPositiveRegularizer, norm_mul,
    Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.smoothTransition.le_one _) (norm_nonneg t)

theorem physicalPositiveRegularizer_eq {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    physicalPositiveRegularizer δ t = t := by
  have hs : 1 ≤ t / δ := (le_div_iff₀ hδ).2 (by simpa only [one_mul] using ht)
  simp only [physicalPositiveRegularizer, Real.smoothTransition.one_of_one_le hs, mul_one]

theorem deriv_physicalPositiveRegularizer (δ t : ℝ) :
    deriv (physicalPositiveRegularizer δ) t = Real.smoothTransition (t / δ) +
      (t / δ) * deriv Real.smoothTransition (t / δ) := by
  have hT := ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable one_ne_zero
    (t / δ)).hasDerivAt
  have hc := (hasDerivAt_id t).mul (hT.comp t ((hasDerivAt_id t).div_const δ))
  calc
    deriv (physicalPositiveRegularizer δ) t =
        1 * Real.smoothTransition (t / δ) + t * (deriv Real.smoothTransition (t / δ) * (1 / δ)) := by
      convert! hc.deriv using 1
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem exists_uniform_bound_deriv_physicalPositiveRegularizer :
    ∃ B : ℝ≥0, ∀ δ t : ℝ, ‖deriv (physicalPositiveRegularizer δ) t‖ ≤ B := by
  obtain ⟨M, hM⟩ := exists_bound_weighted_deriv_smoothTransition
  refine ⟨1 + M, fun δ t => ?_⟩
  rw [deriv_physicalPositiveRegularizer]
  calc
    ‖Real.smoothTransition (t / δ) + (t / δ) * deriv Real.smoothTransition (t / δ)‖ ≤
        ‖Real.smoothTransition (t / δ)‖ + ‖(t / δ) * deriv Real.smoothTransition (t / δ)‖ := norm_add_le _ _
    _ ≤ 1 + M := add_le_add
      (by rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)];
          exact Real.smoothTransition.le_one _) (hM _)
    _ = _ := by simp

theorem deriv_physicalPositiveRegularizer_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : δ < t) :
    deriv (physicalPositiveRegularizer δ) t = 1 := by
  have hs : 1 < t / δ := (lt_div_iff₀ hδ).2 (by simpa only [one_mul] using ht)
  simp only [deriv_physicalPositiveRegularizer, Real.smoothTransition.one_of_one_le hs.le,
    deriv_smoothTransition_of_one_lt hs, mul_zero, add_zero]

end

end BernsteinObstacle
