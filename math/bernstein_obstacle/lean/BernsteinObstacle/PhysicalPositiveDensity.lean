import BernsteinObstacle.PhysicalZeroSetGradient
import BernsteinObstacle.PhysicalPositiveRegularizer

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

theorem tendsto_eLpNorm_comp_uniform_lipschitz
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : ℕ → α → ℝ} {f : α → ℝ}
    {Φ : ℕ → ℝ → ℝ} {B : ℝ≥0} (hΦ : ∀ n, LipschitzWith B (Φ n))
    (hlim : Tendsto (fun n => eLpNorm (u n - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Φ n (u n x) - Φ n (f x)) 2 μ)
      atTop (𝓝 0) := by
  have hdom : Tendsto (fun n => ‖(B : ℝ)‖ₑ * eLpNorm (u n - f) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (enorm_ne_top : ‖(B : ℝ)‖ₑ ≠ ∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    hdom (fun _ => bot_le)
  intro n
  calc
    eLpNorm (fun x => Φ n (u n x) - Φ n (f x)) 2 μ ≤ eLpNorm ((B : ℝ) • (u n - f)) 2 μ := by
      apply eLpNorm_mono
      intro x
      simpa only [Pi.smul_apply, Pi.sub_apply, norm_smul,
        Real.norm_of_nonneg B.coe_nonneg] using (hΦ n).norm_sub_le (u n x) (f x)
    _ = _ := eLpNorm_const_smul _ _ _ _

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive C-infinity compactly supported functions are actually dense
in the full nonnegative H01 cone on every open set. This constructs both
value and weak-gradient L2 limits from ordinary H01 approximation data.
Neither positive density nor a positive-part chain rule is assumed. The
proof uses a single a.e.-convergent subsequence and uniform scalar
regularizers; at the zero level the proved actual weak gradient vanishes. -/
theorem nonempty_nonnegativeH01ApproximationWitness_of_memH01
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : SobolevH01Port.MemH01 u Ω)
    (hpos : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u x) :
    Nonempty (SobolevH01Port.NonnegativeH01ApproximationWitness u Ω) := by
  rcases hu.2 with ⟨hw, φ, hφ, hc, hs, hfun, hgrad⟩
  let μ := volume.restrict Ω
  have hφmem (n : ℕ) : MemLp (φ n) 2 μ :=
    ((hφ n).continuous.memLp_of_hasCompactSupport (hc n)).restrict Ω
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_L2_convergence
    (fun n => (hφmem n).1) hw.memLp.1 hfun
  obtain ⟨B, hB⟩ := exists_uniform_bound_deriv_physicalPositiveRegularizer
  let Φ : ℕ → ℝ → ℝ := fun n => physicalPositiveRegularizer (physicalSmoothingScale n)
  let w : ℕ → E → ℝ := fun n => Φ n ∘ φ (ns n)
  have hΦ (n : ℕ) : ContDiff ℝ 1 (Φ n) :=
    (contDiff_physicalPositiveRegularizer _).of_le (by simp)
  have hLip (n : ℕ) : LipschitzWith B (Φ n) :=
    lipschitzWith_of_contDiff_deriv_bound (hΦ n) B (hB _)
  have hΦu (n : ℕ) : AEStronglyMeasurable (fun x => Φ n (u x)) μ :=
    (hΦ n).continuous.comp_aestronglyMeasurable hw.memLp.1
  have hfirst := tendsto_eLpNorm_comp_uniform_lipschitz hLip
    (hfun.comp hns.tendsto_atTop)
  have hsecond : Tendsto (fun n => eLpNorm (fun x => Φ n (u x) - u x) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => (hΦu n).sub hw.memLp.1) hw.memLp 2
    · intro n
      filter_upwards [] with x
      change ‖Φ n (u x) - u x‖ ≤ (2 : ℝ) * ‖u x‖
      calc
        ‖Φ n (u x) - u x‖ ≤ ‖Φ n (u x)‖ + ‖u x‖ := norm_sub_le _ _
        _ ≤ ‖u x‖ + ‖u x‖ := add_le_add (norm_physicalPositiveRegularizer_le _ _) (le_refl _)
        _ = _ := by ring
    · filter_upwards [hpos] with x hx
      by_cases hx0 : u x = 0
      · simp only [Pi.sub_apply, hx0, Φ, physicalPositiveRegularizer_zero, sub_zero]
        exact tendsto_const_nhds
      · have hxp : 0 < u x := lt_of_le_of_ne hx (Ne.symm hx0)
        have he := tendsto_physicalSmoothingScale.eventually_lt_const hxp
        apply (tendsto_congr' (show (fun n => Φ n (u x) - u x) =ᶠ[atTop]
          (fun _ : ℕ => 0) from ?_)).2 tendsto_const_nhds
        filter_upwards [he] with n hn
        rw [show Φ n (u x) = u x from physicalPositiveRegularizer_eq
          (physicalSmoothingScale_pos n) hn.le, sub_self]
  have hsum := tendsto_eLpNorm_add_of_limits
    (fun n => ((hΦ n).continuous.comp_aestronglyMeasurable (hφmem (ns n)).1).sub (hΦu n))
    (fun n => (hΦu n).sub hw.memLp.1) hfirst hsecond
  have hwfun : Tendsto (fun n => eLpNorm (fun x => w n x - u x) 2 μ) atTop (𝓝 0) := by
    apply hsum.congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.add_apply, Pi.sub_apply, w, Function.comp_apply]
    ring
  have hwgrad (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (w n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 μ) atTop (𝓝 0) := by
    let D : ℕ → E → ℝ := fun n x => (fderiv ℝ (φ (ns n)) x) (EuclideanSpace.single i 1)
    let q : ℕ → E → ℝ := fun n x => deriv (Φ n) (φ (ns n) x)
    let G : E → ℝ := fun x => hw.weakGrad x i
    have hG : MemLp G 2 μ := hw.weakGrad_component_memLp i
    have hD (n : ℕ) : MemLp (D n) 2 μ :=
      ((((hφ (ns n)).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hc (ns n)).fderiv_apply (𝕜 := ℝ)
          (EuclideanSpace.single i 1))).restrict Ω
    have hq (n : ℕ) : AEStronglyMeasurable (q n) μ :=
      ((hΦ n).continuous_deriv (by simp)).comp_aestronglyMeasurable (hφmem (ns n)).1
    have hqB (n : ℕ) : ∀ᵐ x ∂μ, ‖q n x‖ ≤ B := Eventually.of_forall fun x => hB _ _
    have hz := weakGrad_component_zero_of_memH01 hΩ hu hw i
    have hfirst := tendsto_eLpNorm_mul_of_ae_bound B hqB
      ((hgrad i).comp hns.tendsto_atTop)
    have hsecond : Tendsto (fun n => eLpNorm (fun x => (q n x - 1) * G x) 2 μ)
        atTop (𝓝 0) := by
      apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
        (fun n => ((hq n).sub aestronglyMeasurable_const).mul hG.1) hG (B + 1)
      · intro n
        filter_upwards [hqB n] with x hx
        rw [Pi.mul_apply, Pi.sub_apply, norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          ‖q n x - 1‖ ≤ ‖q n x‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
          _ ≤ (B : ℝ) + 1 := add_le_add hx (by simp)
          _ = _ := by simp
      · filter_upwards [hae, hpos, hz] with x hx hpx hzx
        by_cases hx0 : u x = 0
        · have hGx : G x = 0 := hzx hx0
          simpa only [Pi.mul_apply, hGx, mul_zero] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        · have hxp : 0 < u x := lt_of_le_of_ne hpx (Ne.symm hx0)
          have ht : Tendsto (fun n => φ (ns n) x - physicalSmoothingScale n) atTop (𝓝 (u x)) := by
            simpa only [sub_zero] using hx.sub tendsto_physicalSmoothingScale
          have he := ht.eventually_const_lt hxp
          apply (tendsto_congr' (show (fun n => ((q n - 1) * G) x) =ᶠ[atTop]
            (fun _ : ℕ => 0) from ?_)).2 tendsto_const_nhds
          filter_upwards [he] with n hn
          have heq : q n x = 1 := deriv_physicalPositiveRegularizer_eq_one
            (physicalSmoothingScale_pos n) (sub_pos.mp hn)
          simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, heq, sub_self, zero_mul]
    have hsum := tendsto_eLpNorm_add_of_limits
      (fun n => (hq n).mul ((hD n).1.sub hG.1))
      (fun n => ((hq n).sub aestronglyMeasurable_const).mul hG.1) hfirst hsecond
    have heq (n : ℕ) (x : E) : (fderiv ℝ (w n) x) (EuclideanSpace.single i 1) =
        q n x * D n x := by
      have hc := ((hΦ n).differentiable one_ne_zero (φ (ns n) x)).hasDerivAt.comp_hasFDerivAt x
        (((hφ (ns n)).differentiable (by simp)) x).hasFDerivAt
      convert! congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hc.fderiv using 1
    apply hsum.congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    rw [heq]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    ring
  refine ⟨{
    weakWitness := hw
    approx := w
    smooth := fun n => (contDiff_physicalPositiveRegularizer _).comp (hφ (ns n))
    compactSupport := fun n => (hc (ns n)).comp_left (physicalPositiveRegularizer_zero _)
    support_subset := fun n => (tsupport_comp_subset (physicalPositiveRegularizer_zero _)
      (φ (ns n))).trans (hs (ns n))
    nonnegative := fun n x => physicalPositiveRegularizer_nonneg (physicalSmoothingScale_pos n) _
    function_tendsto := hwfun
    gradient_tendsto := hwgrad
  }⟩

/-- A genuine positive-density witness for every nonnegative H01 input,
chosen from the proved existence theorem rather than requested as a premise. -/
def physicalNonnegativeH01ApproximationWitness
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : SobolevH01Port.MemH01 u Ω)
    (hpos : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u x) :
    SobolevH01Port.NonnegativeH01ApproximationWitness u Ω :=
  Classical.choice (nonempty_nonnegativeH01ApproximationWitness_of_memH01 hΩ hu hpos)

end

end BernsteinObstacle
