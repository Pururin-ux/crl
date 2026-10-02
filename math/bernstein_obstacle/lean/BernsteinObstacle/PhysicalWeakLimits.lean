import BernsteinObstacle.PhysicalWeakDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Function Filter Topology
open scoped ENNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Scalar integral pairing is the actual L2 inner product of equivalence
classes; changing representatives does not change the integral. -/
theorem integral_mul_eq_L2_inner {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) = ⟪hf.toLp f, hg.toLp g⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

/-- Strong L2 convergence gives convergence of the actual integral pairing
with every fixed L2 test function, by continuity of the Hilbert inner product. -/
theorem tendsto_integral_mul_of_L2_convergence
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g φ : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : MemLp g 2 μ) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * φ x ∂μ) atTop (𝓝 (∫ x, g x * φ x ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hlim
  simpa only [← integral_mul_eq_L2_inner] using
    hLp.inner (𝕜 := ℝ)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => hφ.toLp φ) atTop (𝓝 (hφ.toLp φ)))

/-- Actual weak partials are closed under joint strong L2 convergence of
functions and derivative components. No weak-limit witness is assumed. -/
theorem hasWeakPartialDeriv_of_L2_limit
    {Ω : Set E} {i : Fin d} {f g : E → ℝ} {u v : ℕ → E → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict Ω))
    (hv : ∀ n, MemLp (v n) 2 (volume.restrict Ω))
    (hweak : ∀ n, SobolevH01Port.HasWeakPartialDeriv i (v n) (u n) Ω)
    (hfun : Tendsto (fun n => eLpNorm (u n - f) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (hgrad : Tendsto (fun n => eLpNorm (v n - g) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    SobolevH01Port.HasWeakPartialDeriv i g f Ω := by
  intro φ hφ hc hs
  let Dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  have hDcont : Continuous Dφ :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport Dφ := hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hDmem : MemLp Dφ 2 (volume.restrict Ω) :=
    (hDcont.memLp_of_hasCompactSupport hDc).restrict Ω
  have hφmem : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hleft := tendsto_integral_mul_of_L2_convergence hu hf hDmem hfun
  have hright := tendsto_integral_mul_of_L2_convergence hv hg hφmem hgrad
  exact tendsto_nhds_unique hleft (hright.neg.congr fun n => (hweak n φ hφ hc hs).symm)

/-- Uniqueness of actual integral-based weak partial derivatives, adapted
from DeGiorgi/SobolevSpace/WeakDerivatives.lean at
4c1b3077d3782b24065184df4ba59501b2e56fc7 (Apache-2.0). The decisive fundamental
lemma is the pinned Mathlib distribution theorem, not a project axiom. -/
theorem ae_eq_of_hasWeakPartialDeriv {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g₁ g₂ f : E → ℝ}
    (h1 : SobolevH01Port.HasWeakPartialDeriv i g₁ f Ω)
    (h2 : SobolevH01Port.HasWeakPartialDeriv i g₂ f Ω)
    (hg₁ : LocallyIntegrable g₁ (volume.restrict Ω))
    (hg₂ : LocallyIntegrable g₂ (volume.restrict Ω)) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  suffices h : ∀ᵐ x ∂volume.restrict Ω, (g₁ - g₂) x = 0 by
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  rw [ae_restrict_iff' hΩ.measurableSet]
  apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hg₁.sub hg₂)
  · intro φ hφ hc hs
    have eq1 := h1 φ hφ hc hs
    have eq2 := h2 φ hφ hc hs
    have heq : ∫ x in Ω, g₁ x * φ x = ∫ x in Ω, g₂ x * φ x := by linarith
    have hzero : ∀ x, x ∉ Ω → φ x • (g₁ - g₂) x = 0 := by
      intro x hx
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp [hφx]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp_rw [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub]
    · simp_rw [mul_comm (φ _)]
      linarith
    · simpa only [smul_eq_mul] using
        hg₁.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    · simpa only [smul_eq_mul] using
        hg₂.integrable_smul_left_of_hasCompactSupport hφ.continuous hc

end

end BernsteinObstacle
