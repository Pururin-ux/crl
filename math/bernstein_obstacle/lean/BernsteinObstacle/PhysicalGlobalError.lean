import BernsteinObstacle.PhysicalH01Recovery
import BernsteinObstacle.PhysicalSimplexGradient
import Mathlib.Analysis.Convex.Measure

open MeasureTheory Set Function Filter Topology
open scoped ENNReal BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual affine element boundaries have Lebesgue measure zero, by the
finite-dimensional convex-set theorem; no null-interface assumption is
added to the physical mesh data. -/
theorem volume_frontier_physicalSimplex (b : AffineBasis (Fin (d + 1)) ℝ E) :
    volume (frontier (Set.range (physicalSimplexPoint b))) = 0 :=
  (convex_range_physicalSimplexPoint b).addHaar_frontier volume

theorem ae_mem_physicalElement_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) :
    ∀ᵐ p ∂volume.restrict (physicalMeshSet b),
      ∃ T, p ∈ interior (Set.range (physicalSimplexPoint (b T))) := by
  have hnull : volume (⋃ T, frontier (Set.range (physicalSimplexPoint (b T)))) = 0 :=
    measure_iUnion_null_iff.mpr fun T => volume_frontier_physicalSimplex (b T)
  have hae : ∀ᵐ p ∂volume, p ∉ ⋃ T, frontier (Set.range (physicalSimplexPoint (b T))) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hnull)
  filter_upwards [ae_restrict_mem (isCompact_physicalMeshSet b).measurableSet,
    ae_restrict_of_ae hae] with p hp hnot
  obtain ⟨T, hpT⟩ := mem_iUnion.mp hp
  refine ⟨T, ?_⟩
  by_contra hno
  apply hnot
  apply mem_iUnion.mpr
  refine ⟨T, ?_⟩
  rw [frontier, (isClosed_range_physicalSimplexPoint_affineBasis (b T)).closure_eq]
  exact ⟨hpT, hno⟩

theorem eLpNorm_physicalMeshRecovery_error_le
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (M h : ℝ) (hM : 0 ≤ M)
    (hdiam : ∀ T i j, ‖b T i - b T j‖ ≤ h)
    (hf : ∀ z ∈ physicalMeshSet b, DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ physicalMeshSet b, ∀ z ∈ physicalMeshSet b,
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖) :
    eLpNorm (fun p => physicalMeshRecovery b n hn f p - f p) 2
      (volume.restrict (physicalMeshSet b)) ≤
      (volume (physicalMeshSet b)) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal (M * h ^ 2) := by
  have hpoint : ∀ᵐ p ∂volume.restrict (physicalMeshSet b),
      ‖physicalMeshRecovery b n hn f p - f p‖ ≤ M * h ^ 2 := by
    filter_upwards [ae_restrict_mem (isCompact_physicalMeshSet b).measurableSet] with p hp
    obtain ⟨T, x, hx⟩ := mem_iUnion.mp hp
    have hsub : Set.range (physicalSimplexPoint (b T)) ⊆ physicalMeshSet b :=
      fun y hy => mem_iUnion.mpr ⟨T, hy⟩
    rw [physicalMeshRecovery_eq_on_element b hb n hn f T p ⟨x, hx⟩, ← hx,
      affineBasisPhysicalSamplingRecovery_eq, Real.norm_eq_abs]
    exact physicalSamplingRecovery_abs_error_le_of_lipschitz_fderiv (b T) n hn f M h
      hM (hdiam T) (fun z hz => hf z (hsub hz))
      (fun y hy z hz => hDf y (hsub hy) z (hsub hz)) x
  simpa using eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hpoint

/-- A genuine global L2 estimate for the assembled gradient. The interfaces
are eliminated by their proved null measure; the local derivative is used
only where neighborhood equality has been established. -/
theorem eLpNorm_gradient_physicalMeshRecovery_error_le
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (M H C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (h : ι → ℝ) (hdiam : ∀ T i j, ‖b T i - b T j‖ ≤ h T)
    (hmax : ∀ T, h T ≤ H)
    (hshape : ∀ T, h T * ∑ i, ‖affineBasisCoordinateDerivative (b T) i‖ ≤ C)
    (hf : ∀ z ∈ physicalMeshSet b, DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ physicalMeshSet b, ∀ z ∈ physicalMeshSet b,
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖) :
    eLpNorm (fun p => gradient (physicalMeshRecovery b n hn f) p - gradient f p) 2
      (volume.restrict (physicalMeshSet b)) ≤
      (volume (physicalMeshSet b)) ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal ((n : ℝ) * M * C * H) := by
  have hpoint : ∀ᵐ p ∂volume.restrict (physicalMeshSet b),
      ‖gradient (physicalMeshRecovery b n hn f) p - gradient f p‖ ≤ (n : ℝ) * M * C * H := by
    filter_upwards [ae_mem_physicalElement_interior b] with p hp
    obtain ⟨T, hpT⟩ := hp
    have hsub : Set.range (physicalSimplexPoint (b T)) ⊆ physicalMeshSet b :=
      fun y hy => mem_iUnion.mpr ⟨T, hy⟩
    obtain ⟨x, hx⟩ := interior_subset hpT
    rw [gradient_physicalMeshRecovery_on_interior b hb n hn f T p hpT, ← hx]
    apply (norm_gradient_affineBasisPhysicalSamplingRecovery_error_le_of_shape
      (b T) n hn f M (h T) C hM (hdiam T) (hshape T)
      (fun z hz => hf z (hsub hz)) (fun y hy z hz => hDf y (hsub hy) z (hsub hz)) x).trans
    exact mul_le_mul_of_nonneg_left (hmax T)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hM) hC)
  simpa using eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hpoint

/-- The two actual L2 terms of the physical H1 error converge for a fixed
degree and a changing finite mesh family with a common closed physical set,
    shrinking maximum diameter and a family-uniform shape bound using each
    element's own size. No comparison of minimum and maximum sizes is assumed.
This is not yet a Hilbert quotient-space or Mosco realization. -/
theorem tendsto_physicalMeshRecovery_H1_error
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0)) (h : ∀ m, κ m → ℝ)
    (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (hshape : ∀ m T, h m T * ∑ i, ‖affineBasisCoordinateDerivative (b m T) i‖ ≤ C)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hDf : ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ M * ‖y - z‖) :
    Tendsto (fun m => eLpNorm (fun p => physicalMeshRecovery (b m) n hn f p - f p)
      2 (volume.restrict S)) atTop (𝓝 0) ∧
    Tendsto (fun m => eLpNorm
      (fun p => gradient (physicalMeshRecovery (b m) n hn f) p - gradient f p)
      2 (volume.restrict S)) atTop (𝓝 0) := by
  have hSc : IsCompact S := by rw [← hsets 0]; exact isCompact_physicalMeshSet (b 0)
  have hV : (volume S) ^ ((2 : ℝ)⁻¹) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hSc.measure_lt_top.ne
  have hfunction := ENNReal.Tendsto.const_mul
    ((ENNReal.continuous_ofReal.tendsto 0).comp
      (by simpa using (hsmall.pow 2).const_mul M)) (Or.inr hV)
  have hgradient := ENNReal.Tendsto.const_mul
    ((ENNReal.continuous_ofReal.tendsto 0).comp
      (by simpa using hsmall.const_mul ((n : ℝ) * M * C))) (Or.inr hV)
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      (by simpa only [ENNReal.ofReal_zero, mul_zero] using hfunction) (fun _ => bot_le)
    intro m
    simpa only [hsets m, Function.comp_def] using! eLpNorm_physicalMeshRecovery_error_le (b m) (hb m) n hn f
      M (H m) hM (fun T i j => (hdiam m T i j).trans (hmax m T)) (by simpa only [hsets m] using hf)
      (by simpa only [hsets m] using hDf)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      (by simpa only [ENNReal.ofReal_zero, mul_zero] using hgradient) (fun _ => bot_le)
    intro m
    simpa only [hsets m, Function.comp_def] using! eLpNorm_gradient_physicalMeshRecovery_error_le (b m) (hb m)
      n hn f M (H m) C hM hC (h m) (hdiam m) (hmax m) (hshape m) (by simpa only [hsets m] using hf)
      (by simpa only [hsets m] using hDf)

end

end BernsteinObstacle
