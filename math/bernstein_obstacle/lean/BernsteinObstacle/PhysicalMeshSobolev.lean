import BernsteinObstacle.PhysicalMeshRecovery
import BernsteinObstacle.PhysicalLocalSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open scoped BigOperators ENNReal
open MeasureTheory Set Filter Topology

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} {ι : Type*}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Integral weak derivatives respect almost-everywhere representatives on
the actual domain. -/
theorem hasWeakPartialDeriv_congr_ae {Ω : Set E} {i : Fin d}
    {f f' g g' : E → ℝ} (h : SobolevH01Port.HasWeakPartialDeriv i g f Ω)
    (hf : f' =ᵐ[volume.restrict Ω] f) (hg : g' =ᵐ[volume.restrict Ω] g) :
    SobolevH01Port.HasWeakPartialDeriv i g' f' Ω := by
  intro φ hφ hcompact hsupport
  calc
    (∫ x in Ω, f' x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
        ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -∫ x in Ω, g x * φ x := h φ hφ hcompact hsupport
    _ = -∫ x in Ω, g' x * φ x := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

theorem memH1_congr_ae {Ω : Set E} {f f' : E → ℝ}
    (h : SobolevH01Port.MemH1 f Ω) (hf : f' =ᵐ[volume.restrict Ω] f) :
    SobolevH01Port.MemH1 f' Ω := by
  refine ⟨(memLp_congr_ae hf).mpr h.1, ?_⟩
  intro i
  obtain ⟨g, hg, hweak⟩ := h.2 i
  exact ⟨g, hg, hasWeakPartialDeriv_congr_ae hweak hf (EventuallyEq.rfl)⟩

/-- Inside an element, the assembled function agrees with its genuine local
polynomial on an entire neighborhood, not only at the evaluation point. -/
theorem eventuallyEq_physicalMeshRecovery_on_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) (p : E)
    (hp : p ∈ interior (Set.range (physicalSimplexPoint (b T)))) :
    physicalMeshRecovery b n hn f =ᶠ[𝓝 p]
      affineBasisPhysicalSamplingRecovery (b T) n hn f := by
  filter_upwards [isOpen_interior.mem_nhds hp] with y hy
  exact physicalMeshRecovery_eq_on_element b hb n hn f T y (interior_subset hy)

theorem fderiv_physicalMeshRecovery_on_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) (p : E)
    (hp : p ∈ interior (Set.range (physicalSimplexPoint (b T)))) :
    fderiv ℝ (physicalMeshRecovery b n hn f) p =
      fderiv ℝ (affineBasisPhysicalSamplingRecovery (b T) n hn f) p :=
  (eventuallyEq_physicalMeshRecovery_on_interior b hb n hn f T p hp).fderiv_eq

theorem gradient_physicalMeshRecovery_on_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) (p : E)
    (hp : p ∈ interior (Set.range (physicalSimplexPoint (b T)))) :
    gradient (physicalMeshRecovery b n hn f) p =
      gradient (affineBasisPhysicalSamplingRecovery (b T) n hn f) p := by
  simp only [gradient, fderiv_physicalMeshRecovery_on_interior b hb n hn f T p hp]

theorem memH1_physicalMeshRecovery_on_element_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) :
    SobolevH01Port.MemH1 (physicalMeshRecovery b n hn f)
      (interior (Set.range (physicalSimplexPoint (b T)))) := by
  apply memH1_congr_ae (memH1_affineBasisPhysicalSamplingRecovery_interior (b T) n hn f)
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  exact physicalMeshRecovery_eq_on_element b hb n hn f T p (interior_subset hp)

/-- The actual classical gradient of the assembled function is its integral
weak gradient on each open element interior. The global interface contribution
is a separate obligation. -/
theorem hasWeakGrad_physicalMeshRecovery_on_element_interior
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) :
    SobolevH01Port.HasWeakGrad (gradient (physicalMeshRecovery b n hn f))
      (physicalMeshRecovery b n hn f)
      (interior (Set.range (physicalSimplexPoint (b T)))) := by
  intro i
  apply hasWeakPartialDeriv_congr_ae
    (hasWeakGrad_affineBasisPhysicalSamplingRecovery (b T) n hn f isOpen_interior i)
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact physicalMeshRecovery_eq_on_element b hb n hn f T p (interior_subset hp)
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    rw [gradient_physicalMeshRecovery_on_interior b hb n hn f T p hp]

variable [Finite ι]

/-- Scalar Lp membership of the actual continuous zero extension, on the
whole ambient physical space. This does not assert global Sobolev membership. -/
theorem memLp_physicalMeshRecovery (q : ℝ≥0∞)
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) :
    MemLp (physicalMeshRecovery b n hn f) q volume := by
  exact (continuous_physicalMeshRecovery b hb hboundary n hn f hf).memLp_of_hasCompactSupport
    (hasCompactSupport_physicalMeshRecovery b n hn f)

end

end BernsteinObstacle
