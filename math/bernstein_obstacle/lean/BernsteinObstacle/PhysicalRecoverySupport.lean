import BernsteinObstacle.PhysicalMeshRecovery
import Mathlib.Topology.MetricSpace.Thickening

open Set Function

namespace BernsteinObstacle

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ}

omit [FiniteDimensional ℝ E] in
/-- A nonzero recovered value requires a nonzero actual lattice sample.
No positivity of the input is assumed. -/
theorem physicalSamplingRecovery_nezero_exists_sample
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (x : BarycentricPoint d) (hx : physicalSamplingRecovery v n hn f x ≠ 0) :
    ∃ α : MultiIndex d n,
      f (physicalSimplexPoint v (simplexLatticePoint d n hn α)) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hx
  simp only [physicalSamplingRecovery, simplexSamplingRecovery, simplexField,
    simplexSamplingCoefficients, hnone, zero_mul, Finset.sum_const_zero]

/-- Recovery cannot propagate a nonzero sample farther than one element
diameter from the actual support of the input. -/
theorem support_physicalMeshRecovery_subset_cthickening
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (h : ℝ)
    (hdiam : ∀ T i j, ‖b T i - b T j‖ ≤ h) :
    support (physicalMeshRecovery b n hn f) ⊆ Metric.cthickening h (tsupport f) := by
  intro p hp
  have hnonzero : physicalMeshRecovery b n hn f p ≠ 0 := mem_support.mp hp
  have hpin : p ∈ physicalMeshSet b := by
    by_contra hnot
    exact hnonzero (physicalMeshRecovery_zero_of_not_mem b n hn f p hnot)
  obtain ⟨T, x, hx⟩ := mem_iUnion.mp hpin
  have hlocal : physicalSamplingRecovery (b T) n hn f x ≠ 0 := by
    rw [physicalMeshRecovery_eq_on_element b hb n hn f T p ⟨x, hx⟩] at hnonzero
    rw [← hx, affineBasisPhysicalSamplingRecovery_eq] at hnonzero
    exact hnonzero
  obtain ⟨α, hα⟩ := physicalSamplingRecovery_nezero_exists_sample (b T) n hn f x hlocal
  apply Metric.mem_cthickening_of_dist_le p
    (physicalSimplexPoint (b T) (simplexLatticePoint d n hn α)) h (tsupport f)
  · exact subset_closure (mem_support.mpr hα)
  · rw [← hx, dist_eq_norm]
    exact physicalSimplexPoint_diameter_le (b T) h (hdiam T) x _

theorem tsupport_physicalMeshRecovery_subset_cthickening
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (h : ℝ)
    (hdiam : ∀ T i j, ‖b T i - b T j‖ ≤ h) :
    tsupport (physicalMeshRecovery b n hn f) ⊆ Metric.cthickening h (tsupport f) := by
  exact closure_minimal
    (support_physicalMeshRecovery_subset_cthickening b hb n hn f h hdiam)
    Metric.isClosed_cthickening

/-- For a compactly supported input inside an open domain, sufficiently
small actual elements keep the recovered support strictly inside the domain.
The radius is independent of the mesh and its element count. -/
theorem exists_radius_physicalMeshRecovery_support_subset
    {Ω : Set E} (hΩ : IsOpen Ω) (f : E → ℝ) (hf : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (b : ι → AffineBasis (Fin (d + 1)) ℝ E), physicalFacesMatch b →
      ∀ (n : ℕ) (hn : 0 < n) (h : ℝ), h ≤ δ →
      (∀ T i j, ‖b T i - b T j‖ ≤ h) →
      tsupport (physicalMeshRecovery b n hn f) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hf.isCompact.exists_cthickening_subset_open hΩ hfs
  refine ⟨δ, hδ, ?_⟩
  intro b hb n hn h hh hdiam
  exact (tsupport_physicalMeshRecovery_subset_cthickening b hb n hn f h hdiam).trans
    ((Metric.cthickening_mono hh (tsupport f)).trans hδΩ)

end

end BernsteinObstacle
