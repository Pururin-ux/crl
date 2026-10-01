import BernsteinObstacle.PhysicalWeakDerivative
import BernsteinObstacle.PhysicalSimplexGeometry

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuinely continuous scalar function belongs to Lp on a compact physical
set for a measure finite on compact sets. -/
theorem memLp_continuous_restrict_compact (q : ℝ≥0∞) {T : Set E}
    (hT : IsCompact T) {f : E → ℝ} (hf : Continuous f)
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] : MemLp f q (μ.restrict T) := by
  haveI : IsFiniteMeasure (μ.restrict T) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hT.measure_lt_top (μ := μ)⟩
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hT.measurableSet] with p hp
  exact hC p hp

/-- This is actual integral-based H1 membership, obtained from C1 and compact
localization, rather than from an assumed Sobolev approximation witness. -/
theorem memH1_of_contDiff_of_subset_compact {Ω T : Set E}
    (hΩ : IsOpen Ω) (hΩT : Ω ⊆ T) (hT : IsCompact T)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) : SobolevH01Port.MemH1 f Ω := by
  constructor
  · exact (memLp_continuous_restrict_compact 2 hT hf.continuous volume).mono_measure
      (Measure.restrict_mono_set volume hΩT)
  · intro i
    refine ⟨fun p => (fderiv ℝ f p) (EuclideanSpace.single i 1), ?_,
      hasWeakPartialDeriv_of_contDiff hΩ hf⟩
    have hcont : Continuous (fun p => (fderiv ℝ f p) (EuclideanSpace.single i 1)) :=
      (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (memLp_continuous_restrict_compact 2 hT hcont volume).mono_measure
      (Measure.restrict_mono_set volume hΩT)

/-- The actual positive sampler belongs to the project's physical H1 space
on the interior of an affine-basis simplex. This does not claim H01 membership
or the assembled finite-element statement. -/
theorem memH1_affineBasisPhysicalSamplingRecovery_interior
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) (f : E → ℝ) :
    SobolevH01Port.MemH1 (affineBasisPhysicalSamplingRecovery b n hn f)
      (interior (Set.range (physicalSimplexPoint b))) := by
  exact memH1_of_contDiff_of_subset_compact isOpen_interior interior_subset
    (isCompact_range_physicalSimplexPoint_affineBasis b)
    (contDiff_affineBasisPhysicalSamplingRecovery 1 b n hn f)

end

end BernsteinObstacle
