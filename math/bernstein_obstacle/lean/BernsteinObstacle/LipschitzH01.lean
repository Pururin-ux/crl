import BernsteinObstacle.WeakMollification

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal Convolution

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A canonical actual weak-gradient witness for a compactly supported
Lipschitz function. All integrability and integration-by-parts data are
proved, rather than supplied as a Sobolev input. -/
def lipschitzH1Witness {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) : SobolevH01Port.MemW1pWitness 2 f Ω := by
  refine ⟨(hf.continuous.memLp_of_hasCompactSupport hc).restrict Ω, gradient f, ?_,
    hasWeakGrad_of_lipschitz_hasCompactSupport hf hc hΩ⟩
  intro i
  simp_rw [gradient_component_eq_fderiv_apply]
  exact (memLp_fderiv_apply_of_lipschitz_hasCompactSupport hf hc 2 _).restrict Ω

theorem physicalMollification_nonneg (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (x : E) :
    0 ≤ physicalMollification δ hδ n f x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg ((physicalShrinkingBump δ hδ n).nonneg_normed t) (hf (x - t))

theorem tendsto_eLpNorm_physicalMollification_function_error
    (δ : ℝ) (hδ : 0 < δ) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f) (Ω : Set E) :
    Tendsto (fun n => eLpNorm (fun x => physicalMollification δ hδ n f x - f x)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hlim := tendsto_eLpNorm_physicalMollification_sub δ hδ
    hf.continuous.aestronglyMeasurable hc (max B 0)
    (fun x => (hB x).trans (le_max_left _ _))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun n => eLpNorm_restrict_le _ 2 volume Ω)

/-- The same smooth sequence converges in every actual derivative component
in L2; the derivative/convolution identity prevents independent choices of
function and gradient approximations. -/
theorem tendsto_eLpNorm_physicalMollification_gradient_error
    (δ : ℝ) (hδ : 0 < δ) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f) (Ω : Set E) (i : Fin d) :
    Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (physicalMollification δ hδ n f) x) (EuclideanSpace.single i 1) -
        (fderiv ℝ f x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  let v : E := EuclideanSpace.single i 1
  have hbound : ∀ x, ‖(fderiv ℝ f x) v‖ ≤ C * ‖v‖ := fun x =>
    ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))
  have hlim := tendsto_eLpNorm_physicalMollification_sub δ hδ
    (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
    (hc.fderiv_apply (𝕜 := ℝ) v) (C * ‖v‖) hbound
  simp_rw [fderiv_physicalMollification_apply δ hδ _ hf hc i]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun n => eLpNorm_restrict_le _ 2 volume Ω)

variable [NeZero d]

/-- Actual H01 membership, witnessed by a concrete normalized-bump sequence
whose supports stay inside Ω and whose function and weak-gradient errors
both converge in L2. Strict interior support is an explicit hypothesis. -/
theorem memH01_of_lipschitz_hasCompactSupport {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hc : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport f ⊆ Ω) : SobolevH01Port.MemH01 f Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hc.isCompact.exists_cthickening_subset_open hΩ hs
  let hw := lipschitzH1Witness hf hc hΩ
  refine ⟨hw.memW1p, hw, fun n => physicalMollification δ hδ n f, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_physicalMollification δ hδ n hf.continuous.locallyIntegrable
  · intro n
    exact hasCompactSupport_physicalMollification δ hδ n hc
  · intro n
    exact (tsupport_physicalMollification_subset δ hδ n f).trans hδΩ
  · exact tendsto_eLpNorm_physicalMollification_function_error δ hδ hf hc Ω
  · intro i
    simp only [hw, lipschitzH1Witness, gradient_component_eq_fderiv_apply]
    exact tendsto_eLpNorm_physicalMollification_gradient_error δ hδ hf hc Ω i

/-- Construct positive smooth-density data for the bounded Lipschitz,
compactly supported subclass. This does not assume or establish density for
every element of the full nonnegative H01 cone. -/
def nonnegativeH01Approximation_of_lipschitz_hasCompactSupport
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (hc : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport f ⊆ Ω) (hnonneg : ∀ x, 0 ≤ f x) :
    SobolevH01Port.NonnegativeH01ApproximationWitness f Ω := by
  let hex := hc.isCompact.exists_cthickening_subset_open hΩ hs
  let δ := Classical.choose hex
  have hδ := (Classical.choose_spec hex).1
  have hδΩ := (Classical.choose_spec hex).2
  refine ⟨lipschitzH1Witness hf hc hΩ, fun n => physicalMollification δ hδ n f,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_physicalMollification δ hδ n hf.continuous.locallyIntegrable
  · intro n
    exact hasCompactSupport_physicalMollification δ hδ n hc
  · intro n
    exact (tsupport_physicalMollification_subset δ hδ n f).trans hδΩ
  · exact fun n x => physicalMollification_nonneg δ hδ n hnonneg x
  · exact tendsto_eLpNorm_physicalMollification_function_error δ hδ hf hc Ω
  · intro i
    simp only [lipschitzH1Witness, gradient_component_eq_fderiv_apply]
    exact tendsto_eLpNorm_physicalMollification_gradient_error δ hδ hf hc Ω i

end

end BernsteinObstacle
