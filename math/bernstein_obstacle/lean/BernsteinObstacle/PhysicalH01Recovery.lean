import BernsteinObstacle.LipschitzH01
import BernsteinObstacle.PhysicalGlobalSobolev
import BernsteinObstacle.PhysicalRecoverySupport

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d] {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual physical recovery is in H01 when its proved global Lipschitz
zero extension has support inside the open domain. The approximation
sequence is constructed by mollification; none is an input. -/
theorem memH01_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω) :
    SobolevH01Port.MemH01 (physicalMeshRecovery b n hn f) Ω := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  exact memH01_of_lipschitz_hasCompactSupport hC
    (hasCompactSupport_physicalMeshRecovery b n hn f) hΩ hs

/-- A single mesh-independent radius guarantees actual H01 membership on
every finite conforming mesh whose elements meet this diameter bound. -/
theorem exists_radius_memH01_physicalMeshRecovery
    {Ω : Set E} (hΩ : IsOpen Ω) (f : E → ℝ) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (b : ι → AffineBasis (Fin (d + 1)) ℝ E), physicalFacesMatch b →
      physicalBoundaryFaces b →
      (∀ p ∈ frontier (physicalMeshSet b), f p = 0) →
      ∀ (n : ℕ) (hn : 0 < n) (h : ℝ), h ≤ δ →
      (∀ T i j, ‖b T i - b T j‖ ≤ h) →
      SobolevH01Port.MemH01 (physicalMeshRecovery b n hn f) Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := exists_radius_physicalMeshRecovery_support_subset
    (ι := ι) hΩ f hc hs
  refine ⟨δ, hδ, ?_⟩
  intro b hb hboundary hf n hn h hh hdiam
  exact memH01_physicalMeshRecovery b hb hboundary n hn f hf hΩ
    (hδΩ b hb n hn h hh hdiam)

/-- Construct nonnegative smooth H01 approximation data for the actual
positive-coefficient mesh recovery with interior support. -/
def physicalMeshNonnegativeH01Approximation
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    (hnonneg : ∀ p ∈ physicalMeshSet b, 0 ≤ f p)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω) :
    SobolevH01Port.NonnegativeH01ApproximationWitness (physicalMeshRecovery b n hn f) Ω := by
  let hex := exists_lipschitzWith_physicalMeshRecovery b hb hboundary n hn f hf
  let C := Classical.choose hex
  have hC := Classical.choose_spec hex
  exact nonnegativeH01Approximation_of_lipschitz_hasCompactSupport hC
    (hasCompactSupport_physicalMeshRecovery b n hn f) hΩ hs
    (physicalMeshRecovery_nonneg b hb n hn f hnonneg)

omit [Finite ι] [NeZero d] in
theorem zero_frontier_of_tsupport_subset_interior (b : ι → AffineBasis (Fin (d + 1)) ℝ E)
    {f : E → ℝ} (hs : tsupport f ⊆ interior (physicalMeshSet b)) :
    ∀ p ∈ frontier (physicalMeshSet b), f p = 0 := by
  intro p hp
  exact image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hs h))

omit [Finite ι] in
/-- For an actual sequence of finite conforming meshes on the same open
domain, shrinking maximum diameter gives eventual H01 membership of the
actual recovery of each fixed compactly supported input. This is a family
membership theorem, not a uniform H1 error or Mosco theorem. -/
theorem eventually_memH01_physicalMeshRecovery
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    {Ω : Set E} (hΩ : IsOpen Ω) (f : E → ℝ) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω)
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (hdomains : ∀ m, interior (physicalMeshSet (b m)) = Ω)
    (h : ℕ → ℝ) (hsmall : Tendsto h atTop (𝓝 0))
    (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m)
    (n : ℕ) (hn : 0 < n) :
    ∀ᶠ m in atTop, SobolevH01Port.MemH01 (physicalMeshRecovery (b m) n hn f) Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hc.isCompact.exists_cthickening_subset_open hΩ hs
  have hsmall' : ∀ᶠ m in atTop, h m ≤ δ :=
    (hsmall.eventually (gt_mem_nhds hδ)).mono fun _ hm => hm.le
  filter_upwards [hsmall'] with m hm
  apply memH01_physicalMeshRecovery (b m) (hb m) (hboundary m) n hn f
    (zero_frontier_of_tsupport_subset_interior (b m) (by simpa only [hdomains m] using hs)) hΩ
  exact (tsupport_physicalMeshRecovery_subset_cthickening (b m) (hb m) n hn f (h m)
    (hdiam m)).trans ((Metric.cthickening_mono hm (tsupport f)).trans hδΩ)

end

end BernsteinObstacle
