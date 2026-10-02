import BernsteinObstacle.PhysicalPositiveRegularizer
import BernsteinObstacle.PhysicalZeroSetGradient

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

/-- A smooth value cutoff vanishing below the positive level delta. Unlike
the unshifted positive regularizer, this gives strictly interior support to a
continuous nonnegative function which is zero outside an open domain. -/
def physicalBoundaryCutoff (δ t : ℝ) : ℝ := physicalPositiveRegularizer δ (t - δ)

theorem contDiff_physicalBoundaryCutoff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalBoundaryCutoff δ) :=
  (contDiff_physicalPositiveRegularizer δ).comp (contDiff_id.sub contDiff_const)

theorem physicalBoundaryCutoff_zero_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    physicalBoundaryCutoff δ t = 0 := by
  unfold physicalBoundaryCutoff physicalPositiveRegularizer
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le), mul_zero]

theorem physicalBoundaryCutoff_zero {δ : ℝ} (hδ : 0 < δ) :
    physicalBoundaryCutoff δ 0 = 0 := physicalBoundaryCutoff_zero_of_le hδ hδ.le

theorem physicalBoundaryCutoff_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ physicalBoundaryCutoff δ t := physicalPositiveRegularizer_nonneg hδ (t - δ)

theorem norm_physicalBoundaryCutoff_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    ‖physicalBoundaryCutoff δ t‖ ≤ ‖t‖ := by
  by_cases htd : t ≤ δ
  · simp only [physicalBoundaryCutoff_zero_of_le hδ htd, norm_zero, norm_nonneg]
  · have hs : 0 ≤ t - δ := sub_nonneg.mpr (le_of_not_ge htd)
    calc
      ‖physicalBoundaryCutoff δ t‖ ≤ ‖t - δ‖ := norm_physicalPositiveRegularizer_le δ _
      _ = t - δ := Real.norm_of_nonneg hs
      _ ≤ t := sub_le_self _ hδ.le
      _ = ‖t‖ := (Real.norm_of_nonneg ht).symm

theorem physicalBoundaryCutoff_eq_sub {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    physicalBoundaryCutoff δ t = t - δ :=
  physicalPositiveRegularizer_eq hδ (by linarith)

theorem deriv_physicalBoundaryCutoff (δ t : ℝ) :
    deriv (physicalBoundaryCutoff δ) t = deriv (physicalPositiveRegularizer δ) (t - δ) := by
  have hc := (((contDiff_physicalPositiveRegularizer δ).of_le (by simp) :
      ContDiff ℝ 1 _).differentiable one_ne_zero (t - δ)).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const δ)
  rw [show physicalBoundaryCutoff δ = (fun x => physicalPositiveRegularizer δ (x - δ)) from rfl]
  simpa only [Function.comp_def, id_eq, mul_one] using hc.deriv

theorem deriv_physicalBoundaryCutoff_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ < t) :
    deriv (physicalBoundaryCutoff δ) t = 1 := by
  rw [deriv_physicalBoundaryCutoff]
  exact deriv_physicalPositiveRegularizer_eq_one hδ (by linarith)

theorem exists_uniform_bound_deriv_physicalBoundaryCutoff :
    ∃ B : ℝ≥0, ∀ δ t : ℝ, ‖deriv (physicalBoundaryCutoff δ) t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_uniform_bound_deriv_physicalPositiveRegularizer
  exact ⟨B, fun δ t => by rw [deriv_physicalBoundaryCutoff]; exact hB δ (t - δ)⟩

theorem tendsto_physicalBoundaryCutoff (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => physicalBoundaryCutoff (physicalSmoothingScale n) t) atTop (𝓝 t) := by
  by_cases ht0 : t = 0
  · subst t
    simpa only [physicalBoundaryCutoff_zero (physicalSmoothingScale_pos _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have he := tendsto_physicalSmoothingScale.eventually_lt_const
      (by linarith : 0 < t / 2)
    have hs : Tendsto (fun n => t - physicalSmoothingScale n) atTop (𝓝 t) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_physicalSmoothingScale
    apply hs.congr'
    filter_upwards [he] with n hn
    exact (physicalBoundaryCutoff_eq_sub (physicalSmoothingScale_pos n) (by linarith)).symm

/-- The topological support is contained in a closed positive level set,
not merely in the open set where the cutoff is nonzero. -/
theorem tsupport_physicalBoundaryCutoff_subset_level {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun x => physicalBoundaryCutoff δ (f x)) ⊆ {x | δ ≤ f x} := by
  apply closure_minimal _ (isClosed_le continuous_const hf)
  intro x hx
  have hn : ¬f x ≤ δ := by
    intro ht
    exact hx (physicalBoundaryCutoff_zero_of_le hδ ht)
  exact (lt_of_not_ge hn).le

theorem tsupport_physicalBoundaryCutoff_subset_domain {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {Ω : Set X} (hz : ∀ x ∉ Ω, f x = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun x => physicalBoundaryCutoff δ (f x)) ⊆ Ω := by
  intro x hx
  have hlevel := tsupport_physicalBoundaryCutoff_subset_level hf hδ hx
  by_contra hnot
  change δ ≤ f x at hlevel
  rw [hz x hnot] at hlevel
  exact (not_le_of_gt hδ) hlevel

end

end BernsteinObstacle
