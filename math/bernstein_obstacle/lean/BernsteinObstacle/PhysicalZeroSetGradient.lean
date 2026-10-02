import BernsteinObstacle.PhysicalC1ChainRule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

/-- Positive scales tending to zero, used by actual scalar regularizations. -/
def physicalSmoothingScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem physicalSmoothingScale_pos (n : ℕ) : 0 < physicalSmoothingScale n := by
  unfold physicalSmoothingScale
  positivity

theorem tendsto_physicalSmoothingScale :
    Tendsto physicalSmoothingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- A smooth probe whose derivative tends to the indicator of the zero level set.
Together with the actual C1 weak chain rule and L2 closure this gives the
zero-set-gradient theorem without assuming a general Stampacchia lemma. -/
def physicalZeroProbe (δ t : ℝ) : ℝ := δ * Real.arctan (t / δ)

@[simp] theorem physicalZeroProbe_zero (δ : ℝ) : physicalZeroProbe δ 0 = 0 := by
  simp [physicalZeroProbe]

theorem contDiff_physicalZeroProbe (δ : ℝ) :
    ContDiff ℝ 1 (physicalZeroProbe δ) :=
  contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const δ))

theorem deriv_physicalZeroProbe {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    deriv (physicalZeroProbe δ) t = 1 / (1 + (t / δ) ^ 2) := by
  have hc := ((Real.hasDerivAt_arctan (t / δ)).comp t
    ((hasDerivAt_id t).div_const δ)).const_mul δ
  calc
    deriv (physicalZeroProbe δ) t = δ * (1 / (1 + (t / δ) ^ 2) * (1 / δ)) := by
      convert! hc.deriv using 1
    _ = _ := by field_simp [hδ]

theorem deriv_physicalZeroProbe_eq {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    deriv (physicalZeroProbe δ) t = δ ^ 2 / (δ ^ 2 + t ^ 2) := by
  rw [deriv_physicalZeroProbe hδ]
  have hden : δ ^ 2 + t ^ 2 ≠ 0 := by
    have hd : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
    nlinarith [sq_nonneg t]
  field_simp
  <;> ring

theorem norm_deriv_physicalZeroProbe_le {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    ‖deriv (physicalZeroProbe δ) t‖ ≤ 1 := by
  rw [deriv_physicalZeroProbe hδ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (t / δ)])

theorem lipschitzWith_physicalZeroProbe {δ : ℝ} (hδ : δ ≠ 0) :
    LipschitzWith 1 (physicalZeroProbe δ) :=
  lipschitzWith_of_contDiff_deriv_bound (contDiff_physicalZeroProbe δ) 1
    (norm_deriv_physicalZeroProbe_le hδ)

theorem norm_physicalZeroProbe_le {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    ‖physicalZeroProbe δ t‖ ≤ ‖t‖ := by
  simpa only [physicalZeroProbe_zero, sub_zero, NNReal.coe_one, one_mul] using
    (lipschitzWith_physicalZeroProbe hδ).norm_sub_le t 0

theorem norm_physicalZeroProbe_le_scale {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    ‖physicalZeroProbe δ t‖ ≤ δ * (Real.pi / 2) := by
  rw [physicalZeroProbe, norm_mul, Real.norm_of_nonneg hδ, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ hδ
  exact (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
    (Real.arctan_lt_pi_div_two _).le⟩)

theorem tendsto_physicalZeroProbe (t : ℝ) :
    Tendsto (fun n => physicalZeroProbe (physicalSmoothingScale n) t) atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun n => norm_physicalZeroProbe_le_scale (physicalSmoothingScale_pos n).le t)
  simpa only [zero_mul] using tendsto_physicalSmoothingScale.mul_const (Real.pi / 2)

theorem tendsto_deriv_physicalZeroProbe (t : ℝ) :
    Tendsto (fun n => deriv (physicalZeroProbe (physicalSmoothingScale n)) t)
      atTop (𝓝 (if t = 0 then 1 else 0)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [deriv_physicalZeroProbe (physicalSmoothingScale_pos _).ne', zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, div_self (by norm_num : (1 : ℝ) ≠ 0),
      ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · have hs := tendsto_physicalSmoothingScale.pow 2
    have hd := hs.div (hs.add_const (t ^ 2)) (by simpa using pow_ne_zero 2 ht)
    change Tendsto (fun n => physicalSmoothingScale n ^ 2 /
      (physicalSmoothingScale n ^ 2 + t ^ 2)) atTop (𝓝 (0 ^ 2 / (0 ^ 2 + t ^ 2))) at hd
    simpa only [deriv_physicalZeroProbe_eq (physicalSmoothingScale_pos _).ne',
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_div, if_neg ht,
      Pi.div_apply] using hd

theorem physicalZeroLevelComponent_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u G : α → ℝ}
    (hu : AEMeasurable u μ) (hG : MemLp G 2 μ) :
    MemLp (fun x => if u x = 0 then G x else 0) 2 μ := by
  let χ : ℝ → ℝ := fun t => if t = 0 then 1 else 0
  have hχ : Measurable χ :=
    Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
  have hc : AEStronglyMeasurable (fun x => χ (u x)) μ :=
    (hχ.comp_aemeasurable hu).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖χ (u x)‖ ≤ (1 : ℝ≥0) := by
    filter_upwards [] with x
    by_cases hx : u x = 0 <;> simp [χ, hx]
  simpa only [χ, ite_mul, one_mul, zero_mul] using
    memLp_mul_of_ae_bound hc hG 1 hb

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Every actual H01 weak partial vanishes almost everywhere on the zero
level set. The arctan probe has L2 function limit zero and L2 gradient limit
equal to the zero-level component. Actual weak-limit closure and uniqueness
therefore force that component to vanish. No level-set measurability of a
chosen raw Sobolev representative or finite-volume hypothesis is assumed. -/
theorem weakGrad_component_zero_of_memH01 {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : SobolevH01Port.MemH01 u Ω)
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict Ω, u x = 0 → hw.weakGrad x i = 0 := by
  let μ := volume.restrict Ω
  let Φ : ℕ → ℝ → ℝ := fun n => physicalZeroProbe (physicalSmoothingScale n)
  let q : ℕ → E → ℝ := fun n x => deriv (Φ n) (u x)
  let G : E → ℝ := fun x => hw.weakGrad x i
  let z : E → ℝ := fun x => if u x = 0 then G x else 0
  have hG : MemLp G 2 μ := hw.weakGrad_component_memLp i
  have hz : MemLp z 2 μ := physicalZeroLevelComponent_memLp hw.memLp.aemeasurable hG
  have hq (n : ℕ) : AEStronglyMeasurable (q n) μ :=
    ((contDiff_physicalZeroProbe _).continuous_deriv (by simp)).comp_aestronglyMeasurable
      hw.memLp.1
  have hqB (n : ℕ) : ∀ᵐ x ∂μ, ‖q n x‖ ≤ 1 :=
    Eventually.of_forall fun x => norm_deriv_physicalZeroProbe_le
      (physicalSmoothingScale_pos n).ne' (u x)
  have hfun : Tendsto (fun n => eLpNorm (fun x => Φ n (u x)) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => (contDiff_physicalZeroProbe _).continuous.comp_aestronglyMeasurable
        hw.memLp.1) hw.memLp 1
    · intro n
      exact Eventually.of_forall fun x => by
        simpa only [NNReal.coe_one, one_mul] using norm_physicalZeroProbe_le
          (physicalSmoothingScale_pos n).ne' (u x)
    · exact Eventually.of_forall fun x => tendsto_physicalZeroProbe (u x)
  have hgrad : Tendsto (fun n => eLpNorm (fun x => q n x * G x - z x) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => ((hq n).mul hG.1).sub hz.1) hG 2
    · intro n
      filter_upwards [hqB n] with x hx
      change ‖q n x * G x - z x‖ ≤ (2 : ℝ) * ‖G x‖
      have hzx : ‖z x‖ ≤ ‖G x‖ := by
        by_cases hx : u x = 0 <;> simp [z, hx]
      calc
        ‖q n x * G x - z x‖ ≤ ‖q n x * G x‖ + ‖z x‖ := norm_sub_le _ _
        _ ≤ ‖G x‖ + ‖G x‖ := by
          gcongr
          simpa only [norm_mul, one_mul] using
            mul_le_mul_of_nonneg_right hx (norm_nonneg (G x))
        _ = 2 * ‖G x‖ := by ring
    · filter_upwards [] with x
      have ht := (tendsto_deriv_physicalZeroProbe (u x)).mul_const (G x)
      have ht' : Tendsto (fun n => q n x * G x) atTop (𝓝 (z x)) := by
        simpa only [q, Φ, z, ite_mul, one_mul, zero_mul] using ht
      simpa only [Pi.sub_apply, Pi.mul_apply, sub_self] using ht'.sub_const (z x)
  have hclosed : SobolevH01Port.HasWeakPartialDeriv i z (fun _ : E => 0) Ω := by
    apply hasWeakPartialDeriv_of_L2_limit (MemLp.zero : MemLp (fun _ : E => (0 : ℝ)) 2 μ)
      hz
      (fun n => memLp_of_lipschitz_zero
        (lipschitzWith_physicalZeroProbe (physicalSmoothingScale_pos n).ne')
        (physicalZeroProbe_zero _) hw.memLp)
      (fun n => memLp_mul_of_ae_bound (hq n) hG 1 (hqB n))
      (fun n => hasWeakPartialDeriv_comp_of_memH01 hΩ hu hw
        (contDiff_physicalZeroProbe _) (physicalZeroProbe_zero _) 1
        (norm_deriv_physicalZeroProbe_le (physicalSmoothingScale_pos n).ne') i)
      (by convert! hfun using 1 <;> simp only [Φ, μ, sub_zero]) hgrad
  have hzero : SobolevH01Port.HasWeakPartialDeriv i (fun _ : E => 0)
      (fun _ : E => 0) Ω := by
    intro ψ hψ hc hs
    simp
  have heq := ae_eq_of_hasWeakPartialDeriv hΩ hclosed hzero
    (hz.locallyIntegrable (by norm_num))
    ((MemLp.zero : MemLp (fun _ : E => (0 : ℝ)) 2 μ).locallyIntegrable (by norm_num))
  filter_upwards [heq] with x hx hux
  simpa only [z, if_pos hux] using hx

end

end BernsteinObstacle
