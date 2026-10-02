import BernsteinObstacle.PhysicalWeakLimits
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

/-- A genuine L2 limit has an almost-everywhere converging subsequence.
The short reduction to pinned Mathlib convergence-in-measure is adapted
from DeGiorgi/PositivePart.lean at
4c1b3077d3782b24065184df4ba59501b2e56fc7 (Apache-2.0). -/
theorem exists_subseq_ae_of_L2_convergence
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : ℕ → α → ℝ} {f : α → ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hf : AEStronglyMeasurable f μ)
    (h : Tendsto (fun n => eLpNorm (u n - f) 2 μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => u (ns n) x) atTop (𝓝 (f x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    hu hf h).exists_seq_tendsto_ae

/-- Dominated L2 convergence with an actual L2 majorant, rather than an
assumed constant bound or a finite-volume hypothesis. This applies in
particular to bounded scalar multipliers of actual weak partials. -/
theorem tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : ℕ → α → ℝ} {G : α → ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hG : MemLp G 2 μ) (B : ℝ≥0)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ B * ‖G x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 2 μ) atTop (𝓝 0) := by
  have hGint : (∫⁻ x, ‖G x‖ₑ ^ (2 : ℕ) ∂μ) < ∞ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hG.2
  have hC : ENNReal.ofReal (B : ℝ) ^ (2 : ℕ) ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsq : Tendsto (fun n => ∫⁻ x, ‖u n x‖ₑ ^ (2 : ℕ) ∂μ) atTop (𝓝 0) := by
    have hD := tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (F := fun n x => ‖u n x‖ₑ ^ (2 : ℕ)) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (B : ℝ) ^ (2 : ℕ) * ‖G x‖ₑ ^ (2 : ℕ))
    apply (by simpa only [lintegral_zero] using hD)
    · intro n
      exact (hu n).aemeasurable.enorm.pow_const 2
    · intro n
      filter_upwards [hbound n] with x hx
      have he : ‖u n x‖ₑ ≤ ENNReal.ofReal (B : ℝ) * ‖G x‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul B.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal hx
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) he 2
    · rw [lintegral_const_mul' _ _ hC]
      exact ENNReal.mul_ne_top hC hGint.ne
    · filter_upwards [hlim] with x hx
      simpa only [enorm_zero, ENNReal.rpow_ofNat,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hx.enorm.ennrpow_const 2
  have hroot := hsq.ennrpow_const (1 / 2 : ℝ)
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat,
    ENNReal.rpow_ofNat, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hroot

theorem memLp_mul_of_ae_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q G : α → ℝ}
    (hq : AEStronglyMeasurable q μ) (hG : MemLp G 2 μ) (B : ℝ≥0)
    (hbound : ∀ᵐ x ∂μ, ‖q x‖ ≤ B) : MemLp (fun x => q x * G x) 2 μ := by
  apply ((hG.norm).const_mul (B : ℝ)).mono' (hq.mul hG.1)
  filter_upwards [hbound] with x hx
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem eLpNorm_mul_le_of_ae_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q G : α → ℝ} (B : ℝ≥0)
    (hbound : ∀ᵐ x ∂μ, ‖q x‖ ≤ B) :
    eLpNorm (fun x => q x * G x) 2 μ ≤ ‖(B : ℝ)‖ₑ * eLpNorm G 2 μ := by
  calc
    eLpNorm (fun x => q x * G x) 2 μ ≤ eLpNorm ((B : ℝ) • G) 2 μ := by
      apply eLpNorm_mono_ae
      filter_upwards [hbound] with x hx
      simp only [norm_mul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg B.coe_nonneg]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖(B : ℝ)‖ₑ * eLpNorm G 2 μ := eLpNorm_const_smul _ _ _ _

theorem tendsto_eLpNorm_mul_of_ae_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q G : ℕ → α → ℝ} (B : ℝ≥0)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖q n x‖ ≤ B)
    (hlim : Tendsto (fun n => eLpNorm (G n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => q n x * G n x) 2 μ) atTop (𝓝 0) := by
  have hdom : Tendsto (fun n => ‖(B : ℝ)‖ₑ * eLpNorm (G n) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (enorm_ne_top : ‖(B : ℝ)‖ₑ ≠ ∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    hdom (fun _ => bot_le)
  exact fun n => eLpNorm_mul_le_of_ae_bound B (hbound n)

theorem memLp_of_lipschitz_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ} {Φ : ℝ → ℝ} {B : ℝ≥0}
    (hΦ : LipschitzWith B Φ) (hΦ0 : Φ 0 = 0) (hu : MemLp u 2 μ) :
    MemLp (fun x => Φ (u x)) 2 μ := by
  apply (hu.norm.const_mul (B : ℝ)).mono' (hΦ.continuous.comp_aestronglyMeasurable hu.1)
  exact Eventually.of_forall fun x => by simpa only [hΦ0, sub_zero] using hΦ.norm_sub_le (u x) 0

theorem tendsto_eLpNorm_comp_lipschitz
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : ℕ → α → ℝ} {f : α → ℝ}
    {Φ : ℝ → ℝ} {B : ℝ≥0} (hΦ : LipschitzWith B Φ)
    (hlim : Tendsto (fun n => eLpNorm (u n - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Φ (u n x) - Φ (f x)) 2 μ) atTop (𝓝 0) := by
  have hdom : Tendsto (fun n => ‖(B : ℝ)‖ₑ * eLpNorm (u n - f) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (enorm_ne_top : ‖(B : ℝ)‖ₑ ≠ ∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    hdom (fun _ => bot_le)
  intro n
  calc
    eLpNorm (fun x => Φ (u n x) - Φ (f x)) 2 μ ≤ eLpNorm ((B : ℝ) • (u n - f)) 2 μ := by
      apply eLpNorm_mono
      intro x
      simpa only [Pi.smul_apply, Pi.sub_apply, norm_smul,
        Real.norm_of_nonneg B.coe_nonneg] using hΦ.norm_sub_le (u n x) (f x)
    _ = _ := eLpNorm_const_smul _ _ _ _

theorem tendsto_eLpNorm_add_of_limits
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : ℕ → α → ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hlimu : Tendsto (fun n => eLpNorm (u n) 2 μ) atTop (𝓝 0))
    (hlimv : Tendsto (fun n => eLpNorm (v n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n + v n) 2 μ) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    (by simpa only [add_zero] using hlimu.add hlimv) (fun _ => bot_le)
  exact fun n => eLpNorm_add_le (hu n) (hv n) (by norm_num : (1 : ℝ≥0∞) ≤ 2)

end

end BernsteinObstacle
