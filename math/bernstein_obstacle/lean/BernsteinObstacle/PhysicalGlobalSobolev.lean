import BernsteinObstacle.PhysicalMeshLipschitz
import BernsteinObstacle.PhysicalMeshSobolev
import BernsteinObstacle.LipschitzWeakDerivative

open scoped ENNReal
open MeasureTheory Set

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual assembled recovery has an actual integral-based weak gradient
on the whole physical domain, including the interfaces in the integral. -/
theorem hasWeakGrad_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) :
    SobolevH01Port.HasWeakGrad (gradient (physicalMeshRecovery b n hn f))
      (physicalMeshRecovery b n hn f) Ω := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  exact hasWeakGrad_of_lipschitz_hasCompactSupport hC
    (hasCompactSupport_physicalMeshRecovery b n hn f) hΩ

/-- Genuine global H1 membership of the actual zero-extended mesh recovery,
including on the whole ambient space by taking Ω = univ. This is not H01 or
the normed changing-space/Mosco realization. -/
theorem memH1_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) : SobolevH01Port.MemH1 (physicalMeshRecovery b n hn f) Ω := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  exact memH1_of_lipschitz_hasCompactSupport hC
    (hasCompactSupport_physicalMeshRecovery b n hn f) hΩ

/-- Construct the explicit physical weak-gradient witness from proved
integrability and integration by parts; no Sobolev witness is an input. -/
def physicalMeshH1Witness
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) :
    SobolevH01Port.MemW1pWitness 2 (physicalMeshRecovery b n hn f) Ω := by
  refine ⟨(memLp_physicalMeshRecovery 2 b hb hboundary n hn f hf).restrict Ω,
    gradient (physicalMeshRecovery b n hn f), ?_,
    hasWeakGrad_physicalMeshRecovery b hb hboundary n hn f hf hΩ⟩
  intro i
  simp_rw [gradient_component_eq_fderiv_apply]
  obtain ⟨C, hC⟩ := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  exact (memLp_fderiv_apply_of_lipschitz_hasCompactSupport hC
    (hasCompactSupport_physicalMeshRecovery b n hn f) 2 _).restrict Ω

end

end BernsteinObstacle
