import BernsteinObstacle.PhysicalLpLimits
import BernsteinObstacle.PhysicalRecoveryHilbert

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

theorem lipschitzWith_of_contDiff_deriv_bound {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (B : ℝ≥0) (hB : ∀ t, ‖deriv Φ t‖ ≤ B) :
    LipschitzWith B Φ := by
  apply lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable one_ne_zero)
  intro t
  exact_mod_cast hB t

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Classical C1 chain rule in the actual integral weak-partial identity.
The IBP/chain-rule route is adapted from DeGiorgi/SobolevChainRule.lean at
4c1b3077d3782b24065184df4ba59501b2e56fc7 (Apache-2.0), using the pinned
scalar-with-Frechet chain rule and the proved physical C1 IBP theorem. -/
theorem hasWeakPartialDeriv_comp_contDiff {Ω : Set E} (hΩ : IsOpen Ω)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (i : Fin d) :
    SobolevH01Port.HasWeakPartialDeriv i
      (fun x => deriv Φ (f x) * (fderiv ℝ f x) (EuclideanSpace.single i 1))
      (fun x => Φ (f x)) Ω := by
  have hw := hasWeakPartialDeriv_of_contDiff hΩ (hΦ.comp hf) (i := i)
  have heq (x : E) :
      (fderiv ℝ (Φ ∘ f) x) (EuclideanSpace.single i 1) =
        deriv Φ (f x) * (fderiv ℝ f x) (EuclideanSpace.single i 1) := by
    have hc := ((hΦ.differentiable one_ne_zero) (f x)).hasDerivAt.comp_hasFDerivAt x
      ((hf.differentiable one_ne_zero) x).hasFDerivAt
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hc.fderiv
  intro ψ hψ hc hs
  simpa only [heq, Function.comp_apply] using hw ψ hψ hc hs

variable [NeZero d]

/-- A bounded C1 scalar derivative gives the actual weak chain rule for
every H01 input. The proof constructs a jointly L2-converging subsequence
of actual classical compositions, then uses the proved weak-limit closure.
No general Sobolev chain rule or zero-set-gradient assertion is an input. -/
theorem hasWeakPartialDeriv_comp_of_memH01 {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : SobolevH01Port.MemH01 u Ω)
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (B : ℝ≥0) (hB : ∀ t, ‖deriv Φ t‖ ≤ B) (i : Fin d) :
    SobolevH01Port.HasWeakPartialDeriv i
      (fun x => deriv Φ (u x) * hw.weakGrad x i) (fun x => Φ (u x)) Ω := by
  rcases hu.2 with ⟨hw', φ, hφ, hc, hs, hfun, hgrad⟩
  let μ := volume.restrict Ω
  have hφmem (n : ℕ) : MemLp (φ n) 2 μ :=
    ((hφ n).continuous.memLp_of_hasCompactSupport (hc n)).restrict Ω
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_L2_convergence
    (fun n => (hφmem n).1) hw'.memLp.1 hfun
  have hLip := lipschitzWith_of_contDiff_deriv_bound hΦ B hB
  let D : ℕ → E → ℝ := fun n x => (fderiv ℝ (φ (ns n)) x) (EuclideanSpace.single i 1)
  let qn : ℕ → E → ℝ := fun n x => deriv Φ (φ (ns n) x)
  let q : E → ℝ := fun x => deriv Φ (u x)
  let G : E → ℝ := fun x => hw'.weakGrad x i
  have hDmem (n : ℕ) : MemLp (D n) 2 μ :=
    (((hφ (ns n)).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc (ns n)).fderiv_apply (𝕜 := ℝ)
        (EuclideanSpace.single i 1)) |>.restrict Ω
  have hqn (n : ℕ) : AEStronglyMeasurable (qn n) μ :=
    (hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable (hφmem (ns n)).1
  have hq : AEStronglyMeasurable q μ :=
    (hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable hw'.memLp.1
  have hG : MemLp G 2 μ := hw'.weakGrad_component_memLp i
  have hqnB (n : ℕ) : ∀ᵐ x ∂μ, ‖qn n x‖ ≤ B :=
    Eventually.of_forall fun x => hB (φ (ns n) x)
  have hqB : ∀ᵐ x ∂μ, ‖q x‖ ≤ B := Eventually.of_forall fun x => hB (u x)
  have hfirst : Tendsto (fun n => eLpNorm
      (fun x => qn n x * (D n x - G x)) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_of_ae_bound B hqnB ((hgrad i).comp hns.tendsto_atTop)
  have hsecond : Tendsto (fun n => eLpNorm
      (fun x => (qn n x - q x) * G x) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => ((hqn n).sub hq).mul hG.1) hG (B + B)
    · intro n
      filter_upwards [hqnB n, hqB] with x hnx hqx
      rw [Pi.mul_apply, Pi.sub_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((norm_sub_le _ _).trans (add_le_add hnx hqx)) (norm_nonneg _)
    · filter_upwards [hae] with x hx
      have hqconv := (hΦ.continuous_deriv (by simp)).tendsto (u x) |>.comp hx
      simpa only [q, qn, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, sub_self,
        zero_mul] using (hqconv.sub_const (q x)).mul_const (G x)
  have hsum := tendsto_eLpNorm_add_of_limits
    (fun n => (hqn n).mul ((hDmem n).1.sub hG.1))
    (fun n => ((hqn n).sub hq).mul hG.1) hfirst hsecond
  have hgradlim : Tendsto (fun n => eLpNorm
      (fun x => qn n x * D n x - q x * G x) 2 μ) atTop (𝓝 0) := by
    apply hsum.congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  have hclosed : SobolevH01Port.HasWeakPartialDeriv i
      (fun x => q x * G x) (fun x => Φ (u x)) Ω := by
    apply hasWeakPartialDeriv_of_L2_limit
      (memLp_of_lipschitz_zero hLip hΦ0 hw'.memLp)
      (memLp_mul_of_ae_bound hq hG B hqB)
      (fun n => memLp_of_lipschitz_zero hLip hΦ0 (hφmem (ns n)))
      (fun n => memLp_mul_of_ae_bound (hqn n) (hDmem n) B (hqnB n))
      (fun n => hasWeakPartialDeriv_comp_contDiff hΩ ((hφ (ns n)).of_le (by simp)) hΦ i)
      (tendsto_eLpNorm_comp_lipschitz hLip (hfun.comp hns.tendsto_atTop)) hgradlim
  have hGeq := ae_eq_of_hasWeakPartialDeriv hΩ (hw'.isWeakGrad i) (hw.isWeakGrad i)
    ((hw'.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  apply hasWeakPartialDeriv_congr_ae hclosed EventuallyEq.rfl
  filter_upwards [hGeq] with x hx
  exact congrArg (fun t => deriv Φ (u x) * t) hx.symm

/-- Actual L2 function and weak-gradient data for the bounded C1 composition. -/
def physicalC1CompositionWitness {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : SobolevH01Port.MemH01 u Ω)
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (B : ℝ≥0) (hB : ∀ t, ‖deriv Φ t‖ ≤ B) :
    SobolevH01Port.MemW1pWitness 2 (fun x => Φ (u x)) Ω where
  memLp := memLp_of_lipschitz_zero
    (lipschitzWith_of_contDiff_deriv_bound hΦ B hB) hΦ0 hw.memLp
  weakGrad := fun x => deriv Φ (u x) • hw.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      memLp_mul_of_ae_bound
        ((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable hw.memLp.1)
        (hw.weakGrad_component_memLp i) B (Eventually.of_forall fun x => hB (u x))
  isWeakGrad := by
    intro i
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      hasWeakPartialDeriv_comp_of_memH01 hΩ hu hw hΦ hΦ0 B hB i

end

end BernsteinObstacle
