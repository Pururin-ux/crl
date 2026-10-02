import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

open MeasureTheory Set Function Filter ContinuousLinearMap Metric Topology
open scoped ENNReal Convolution Pointwise

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-!
Bounded compactly supported mollification on the actual Euclidean space.
The support calculation and shrinking bump construction follow the
Apache-2.0 DeGiorgi/SobolevSpace/Approximation.lean, commit
4c1b3077d3782b24065184df4ba59501b2e56fc7. The L2 convergence proof here uses
Mathlib's a.e. convolution limit and dominated convergence for a common
compact support, rather than importing that older package's Lp machinery.
-/

def physicalShrinkingBump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (δ / ((n : ℝ) + 1)) / 2
  rOut := δ / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpos : 0 < δ / ((n : ℝ) + 1) := by positivity
    linarith

theorem physicalShrinkingBump_rOut_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (physicalShrinkingBump (d := d) δ hδ n).rOut ≤ δ := by
  exact div_le_self hδ.le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem tendsto_physicalShrinkingBump_rOut (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (physicalShrinkingBump (d := d) δ hδ n).rOut) atTop (𝓝 0) := by
  simpa [physicalShrinkingBump, div_eq_mul_inv, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ

def physicalMollification (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : E → ℝ) : E → ℝ :=
  (physicalShrinkingBump δ hδ n).normed volume ⋆[lsmul ℝ ℝ, volume] f

theorem tsupport_normedBumpConvolution_subset (φ : ContDiffBump (0 : E)) (f : E → ℝ) :
    tsupport (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) ⊆
      Metric.cthickening φ.rOut (tsupport f) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  have hsum := support_convolution_subset (L := lsmul ℝ ℝ) (μ := volume) hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hsum
  have ha_ball : a ∈ ball (0 : E) φ.rOut := by
    simpa only [φ.support_normed_eq] using ha
  apply Metric.mem_cthickening_of_dist_le (a + b) b φ.rOut (tsupport f)
    (subset_tsupport f hb)
  simpa only [dist_eq_norm, add_sub_cancel_right, sub_zero] using
    (Metric.mem_ball.mp ha_ball).le

theorem tsupport_physicalMollification_subset (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (f : E → ℝ) :
    tsupport (physicalMollification δ hδ n f) ⊆ Metric.cthickening δ (tsupport f) :=
  (tsupport_normedBumpConvolution_subset _ f).trans
    (cthickening_mono (physicalShrinkingBump_rOut_le δ hδ n) (tsupport f))

theorem norm_normedBumpConvolution_le (φ : ContDiffBump (0 : E)) (f : E → ℝ)
    (B : ℝ) (hf : ∀ x, ‖f x‖ ≤ B) (x : E) :
    ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x‖ ≤ B := by
  calc
    ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x‖ ≤
        ∫ t, φ.normed volume t * B := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const B)
      filter_upwards [] with t
      simp only [lsmul_apply, smul_eq_mul, norm_mul,
        Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hf (x - t)) (φ.nonneg_normed t)
    _ = B := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem contDiff_physicalMollification (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    {f : E → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ENat) (physicalMollification δ hδ n f) :=
  (physicalShrinkingBump δ hδ n).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (physicalShrinkingBump δ hδ n).contDiff_normed hf

theorem hasCompactSupport_physicalMollification (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (physicalMollification δ hδ n f) :=
  (physicalShrinkingBump δ hδ n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hf

/-- L2 convergence of a single normalized bump sequence for bounded,
compactly supported measurable functions, including discontinuous weak
derivative components. -/
theorem tendsto_eLpNorm_physicalMollification_sub (δ : ℝ) (hδ : 0 < δ)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hc : HasCompactSupport f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) :
    Tendsto (fun n => eLpNorm (fun x => physicalMollification δ hδ n f x - f x)
      2 volume) atTop (𝓝 0) := by
  have hmem : MemLp f 2 volume := hc.memLp_of_bound hf B (ae_of_all _ hbound)
  have hloc := hmem.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let S := Metric.cthickening δ (tsupport f)
  have hSc : IsCompact S := hc.isCompact.cthickening (r := δ)
  have hmeas : ∀ n, AEStronglyMeasurable (physicalMollification δ hδ n f) volume :=
    fun n => (contDiff_physicalMollification δ hδ n hloc).continuous.aestronglyMeasurable
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => physicalMollification δ hδ n f x) atTop (𝓝 (f x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (tendsto_physicalShrinkingBump_rOut δ hδ) (K := 2) _ hloc
    filter_upwards [] with n
    dsimp [physicalShrinkingBump]
    linarith
  have hsq : Tendsto
      (fun n => ∫⁻ x, ‖physicalMollification δ hδ n f x - f x‖ₑ ^ (2 : ℕ) ∂volume)
      atTop (𝓝 0) := by
    have hD := tendsto_lintegral_of_dominated_convergence'
      (μ := volume) (F := fun n x => ‖physicalMollification δ hδ n f x - f x‖ₑ ^ (2 : ℕ))
      (f := fun _ => 0) (S.indicator fun _ => ENNReal.ofReal (2 * B) ^ (2 : ℕ))
    apply (by simpa only [lintegral_zero] using hD)
    · intro n
      exact ((hmeas n).aemeasurable.sub hf.aemeasurable).enorm.pow_const 2
    · intro n
      filter_upwards [] with x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        apply pow_le_pow_left₀ (by positivity)
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        calc
          ‖physicalMollification δ hδ n f x - f x‖ ≤
              ‖physicalMollification δ hδ n f x‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (norm_normedBumpConvolution_le _ f B hbound x) (hbound x)
          _ = 2 * B := by ring
      · have hm : physicalMollification δ hδ n f x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_physicalMollification_subset
            δ hδ n f h))
        have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
          hx (self_subset_cthickening (tsupport f) h))
        simp [hm, hfx, indicator_of_notMem hx]
    · rw [lintegral_indicator_const hSc.measurableSet]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hSc.measure_lt_top.ne
    · filter_upwards [hlim] with x hx
      simpa only [sub_self, enorm_zero, ENNReal.rpow_ofNat,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2), zero_pow
        (by norm_num : (2 : ℕ) ≠ 0)] using
        (hx.sub_const (f x)).enorm.ennrpow_const 2
  have hroot := hsq.ennrpow_const (1 / 2 : ℝ)
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat,
    ENNReal.rpow_ofNat, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hroot

end

end BernsteinObstacle
