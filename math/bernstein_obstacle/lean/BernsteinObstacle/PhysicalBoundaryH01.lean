import BernsteinObstacle.PhysicalBoundaryCutoff
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A globally nonnegative function has zero classical gradient at every
zero, including the default derivative at a nondifferentiable point. -/
theorem gradient_eq_zero_of_nonneg_zero {f : E → ℝ} (hp : ∀ x, 0 ≤ f x)
    {x : E} (hx : f x = 0) (i : Fin d) : gradient f x i = 0 := by
  have hm : IsLocalMin f x := by
    change ∀ᶠ y in 𝓝 x, f x ≤ f y
    exact Eventually.of_forall fun y => by rw [hx]; exact hp y
  rw [gradient_component_eq_fderiv_apply, hm.fderiv_eq_zero]
  rfl

/-- Pointwise classical chain rule where the globally Lipschitz input is
differentiable. This does not assume that the input already belongs to H01. -/
theorem gradient_comp_contDiff_of_differentiableAt {f : E → ℝ} {x : E}
    (hx : DifferentiableAt ℝ f x) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (i : Fin d) :
    gradient (fun y => Φ (f y)) x i = deriv Φ (f x) * gradient f x i := by
  simp only [gradient_component_eq_fderiv_apply]
  have hc := ((hΦ.differentiable one_ne_zero) (f x)).hasDerivAt.comp_hasFDerivAt x
    hx.hasFDerivAt
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, Function.comp_def] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hc.fderiv

variable [NeZero d]

/-- Boundary-touching nonnegative compact Lipschitz functions belong to the
actual H01 closure if their global zero extension vanishes outside the open
domain. Positive-level cutoffs have interior support; Rademacher's theorem
and dominated L2 convergence prove convergence of their actual gradients.
No H01 or Sobolev chain-rule conclusion is assumed for the original input. -/
theorem memH01_of_nonneg_lipschitz_zero_outside {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f) {Ω : Set E} (hΩ : IsOpen Ω)
    (hz : ∀ x ∉ Ω, f x = 0) (hp : ∀ x, 0 ≤ f x) : SobolevH01Port.MemH01 f Ω := by
  obtain ⟨B, hB⟩ := exists_uniform_bound_deriv_physicalBoundaryCutoff
  let fn : ℕ → E → ℝ := fun n x => physicalBoundaryCutoff (physicalSmoothingScale n) (f x)
  have hΦ (n : ℕ) : ContDiff ℝ 1 (physicalBoundaryCutoff (physicalSmoothingScale n)) :=
    (contDiff_physicalBoundaryCutoff _).of_le (by simp)
  have hLip (n : ℕ) : LipschitzWith (B * C) (fn n) :=
    (lipschitzWith_of_contDiff_deriv_bound (hΦ n) B (hB _)).comp hf
  have hCompact (n : ℕ) : HasCompactSupport (fn n) :=
    hc.comp_left (physicalBoundaryCutoff_zero (physicalSmoothingScale_pos n))
  have hInterior (n : ℕ) : tsupport (fn n) ⊆ Ω :=
    tsupport_physicalBoundaryCutoff_subset_domain hf.continuous hz (physicalSmoothingScale_pos n)
  let wn : ∀ n, SobolevH01Port.MemW1pWitness 2 (fn n) Ω :=
    fun n => lipschitzH1Witness (hLip n) (hCompact n) hΩ
  let w0 := lipschitzH1Witness hf hc hΩ
  let μ := volume.restrict Ω
  have hDiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
    ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume))
  have hChain (n : ℕ) (i : Fin d) : ∀ᵐ x ∂μ,
      (wn n).weakGrad x i =
        deriv (physicalBoundaryCutoff (physicalSmoothingScale n)) (f x) * w0.weakGrad x i := by
    filter_upwards [hDiff] with x hx
    exact gradient_comp_contDiff_of_differentiableAt hx (hΦ n) i
  have hFunction : Tendsto (fun n => eLpNorm (fn n - f) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => (wn n).memLp.1.sub w0.memLp.1) w0.memLp 2
    · intro n
      filter_upwards [] with x
      calc
        ‖fn n x - f x‖ ≤ ‖fn n x‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ ‖f x‖ + ‖f x‖ := add_le_add
          (norm_physicalBoundaryCutoff_le (physicalSmoothingScale_pos n) (hp x)) le_rfl
        _ = (2 : ℝ≥0) * ‖f x‖ := by norm_num; ring
    · filter_upwards [] with x
      simpa only [fn, Pi.sub_apply, sub_self] using
        (tendsto_physicalBoundaryCutoff (f x) (hp x)).sub_const (f x)
  have hGradient (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => (wn n).weakGrad x i - w0.weakGrad x i) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_of_ae_tendsto_of_L2_bound
      (fun n => ((wn n).weakGrad_component_memLp i).1.sub
        (w0.weakGrad_component_memLp i).1) (w0.weakGrad_component_memLp i) (B + 1)
    · intro n
      filter_upwards [hChain n i] with x hx
      simp only [Pi.sub_apply]
      rw [hx]
      calc
        ‖deriv (physicalBoundaryCutoff (physicalSmoothingScale n)) (f x) *
            w0.weakGrad x i - w0.weakGrad x i‖ ≤
            ‖deriv (physicalBoundaryCutoff (physicalSmoothingScale n)) (f x) *
              w0.weakGrad x i‖ + ‖w0.weakGrad x i‖ := norm_sub_le _ _
        _ = ‖deriv (physicalBoundaryCutoff (physicalSmoothingScale n)) (f x)‖ *
            ‖w0.weakGrad x i‖ + ‖w0.weakGrad x i‖ := by rw [norm_mul]
        _ ≤ (B : ℝ) * ‖w0.weakGrad x i‖ + ‖w0.weakGrad x i‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _)) le_rfl
        _ = ((B + 1 : ℝ≥0) : ℝ) * ‖w0.weakGrad x i‖ := by
          simp only [NNReal.coe_add, NNReal.coe_one]; ring
    · filter_upwards [hDiff] with x hx
      change Tendsto (fun n => (wn n).weakGrad x i - w0.weakGrad x i) atTop (𝓝 0)
      have heq (n : ℕ) : (wn n).weakGrad x i =
          deriv (physicalBoundaryCutoff (physicalSmoothingScale n)) (f x) * w0.weakGrad x i :=
        gradient_comp_contDiff_of_differentiableAt hx (hΦ n) i
      by_cases hx0 : f x = 0
      · have hg : w0.weakGrad x i = 0 := gradient_eq_zero_of_nonneg_zero hp hx0 i
        simpa only [heq, hg, mul_zero, sub_self] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · have hpx : 0 < f x := lt_of_le_of_ne (hp x) (Ne.symm hx0)
        have he := tendsto_physicalSmoothingScale.eventually_lt_const
          (by linarith : 0 < f x / 2)
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with n hn
        rw [heq n, deriv_physicalBoundaryCutoff_eq_one (physicalSmoothingScale_pos n)
          (by linarith : 2 * physicalSmoothingScale n < f x), one_mul, sub_self]
  have hConv : Tendsto (fun n => physicalH1OfWitness (wn n)) atTop
      (𝓝 (physicalH1OfWitness w0)) :=
    (tendsto_physicalH1OfWitness_iff wn w0).mpr ⟨hFunction, hGradient⟩
  have hMem (n : ℕ) : physicalH1OfWitness (wn n) ∈ physicalH01Submodule Ω hΩ :=
    (physicalH1OfWitness_mem_H01_iff hΩ (wn n)).mpr
      (memH01_of_lipschitz_hasCompactSupport (hLip n) (hCompact n) hΩ (hInterior n))
  exact (physicalH1OfWitness_mem_H01_iff hΩ w0).mp
    ((isClosed_physicalH01Submodule Ω hΩ).mem_of_tendsto hConv (Eventually.of_forall hMem))

/-- The signed version follows from positive and negative parts in the
actual H01 linear subspace. Equality of function classes identifies the
entire H1 element by the already proved uniqueness of weak derivatives. -/
theorem memH01_of_lipschitz_zero_outside {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f) {Ω : Set E} (hΩ : IsOpen Ω)
    (hz : ∀ x ∉ Ω, f x = 0) : SobolevH01Port.MemH01 f Ω := by
  let fp : E → ℝ := fun x => max (f x) 0
  let fm : E → ℝ := fun x => max (-f x) 0
  have hpl : LipschitzWith C fp := by
    simpa only [fp, max_eq_left (show 0 ≤ C from zero_le)] using hf.max (LipschitzWith.const 0)
  have hml : LipschitzWith C fm := by
    simpa only [fm, max_eq_left (show 0 ≤ C from zero_le), Pi.neg_apply] using
      hf.neg.max (LipschitzWith.const 0)
  have hpc : HasCompactSupport fp :=
    hc.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hmc : HasCompactSupport fm :=
    hc.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have hpMem : SobolevH01Port.MemH01 fp Ω :=
    memH01_of_nonneg_lipschitz_zero_outside hpl hpc hΩ
      (fun x hx => by simp only [fp, hz x hx, max_self]) (fun x => le_max_right _ _)
  have hmMem : SobolevH01Port.MemH01 fm Ω :=
    memH01_of_nonneg_lipschitz_zero_outside hml hmc hΩ
      (fun x hx => by simp only [fm, hz x hx, neg_zero, max_self]) (fun x => le_max_right _ _)
  let wp := lipschitzH1Witness hpl hpc hΩ
  let wm := lipschitzH1Witness hml hmc hΩ
  let w0 := lipschitzH1Witness hf hc hΩ
  have heq : f = fp - fm := by
    funext x
    change f x = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]
  have helement : physicalH1OfWitness w0 = physicalH1OfWitness wp - physicalH1OfWitness wm := by
    apply physicalH1_function_injective hΩ
    change w0.memLp.toLp f = wp.memLp.toLp fp - wm.memLp.toLp fm
    rw [← MemLp.toLp_sub wp.memLp wm.memLp]
    apply Lp.ext
    filter_upwards [w0.memLp.coeFn_toLp, (wp.memLp.sub wm.memLp).coeFn_toLp] with x hx hy
    rw [hx, hy]
    exact congrFun heq x
  apply (physicalH1OfWitness_mem_H01_iff hΩ w0).mp
  rw [helement]
  exact (physicalH01Submodule Ω hΩ).sub_mem
    ((physicalH1OfWitness_mem_H01_iff hΩ wp).mpr hpMem)
    ((physicalH1OfWitness_mem_H01_iff hΩ wm).mpr hmMem)

/-- The continuous physical sampling recovery is an actual H01 function on
the mesh interior even when its support touches the boundary. Face matching
and boundary sampling data construct the global Lipschitz zero extension. -/
theorem memH01_physicalMeshRecovery_on_interior {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) :
    SobolevH01Port.MemH01 (physicalMeshRecovery b n hn f) (interior (physicalMeshSet b)) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  apply memH01_of_lipschitz_zero_outside hC (hasCompactSupport_physicalMeshRecovery b n hn f)
    isOpen_interior
  intro x hx
  by_cases hxs : x ∈ physicalMeshSet b
  · apply physicalMeshRecovery_zero_frontier b hb hboundary n hn f hf x
    change x ∈ closure (physicalMeshSet b) ∧ x ∉ interior (physicalMeshSet b)
    exact ⟨subset_closure hxs, hx⟩
  · exact physicalMeshRecovery_zero_of_not_mem b n hn f x hxs

end

end BernsteinObstacle
