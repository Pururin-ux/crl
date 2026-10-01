import BernsteinObstacle.PhysicalSimplexFaces
import BernsteinObstacle.PhysicalPolynomialSmooth
import BernsteinObstacle.PhysicalSimplexGeometry
import Mathlib.Topology.LocallyFinite

open Set Function

namespace BernsteinObstacle

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ}

/-- Union of actual closed affine-basis elements. -/
def physicalMeshSet (b : ι → AffineBasis (Fin (d + 1)) ℝ E) : Set E :=
  ⋃ T, Set.range (physicalSimplexPoint (b T))

/-- A geometric conformity condition: each overlap point has a common
physical subface with the same ordered vertices. It assumes neither field
continuity nor equality of recovered values. Lower-dimensional intersections
and the diagonal whole-element case are included. -/
def physicalFacesMatch (b : ι → AffineBasis (Fin (d + 1)) ℝ E) : Prop :=
  ∀ T U p, p ∈ Set.range (physicalSimplexPoint (b T)) →
    p ∈ Set.range (physicalSimplexPoint (b U)) →
    ∃ (k : ℕ) (qT : SimplexSubface k d) (qU : SimplexSubface k d)
      (x : BarycentricPoint k),
      qT.vertices (fun i => b T i) = qU.vertices (fun i => b U i) ∧
      physicalSimplexPoint (b T) (qT.point x) = p ∧
      physicalSimplexPoint (b U) (qU.point x) = p

/-- Actual element selection, with zero outside the mesh. Face agreement makes
the selected value independent of the choice. -/
def physicalMeshRecovery (b : ι → AffineBasis (Fin (d + 1)) ℝ E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (p : E) : ℝ := by
  classical
  exact if hp : ∃ T, p ∈ Set.range (physicalSimplexPoint (b T)) then
    affineBasisPhysicalSamplingRecovery (b (Classical.choose hp)) n hn f p
  else 0

theorem physicalMeshRecovery_eq_on_element
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) (p : E)
    (hp : p ∈ Set.range (physicalSimplexPoint (b T))) :
    physicalMeshRecovery b n hn f p = affineBasisPhysicalSamplingRecovery (b T) n hn f p := by
  classical
  have hex : ∃ U, p ∈ Set.range (physicalSimplexPoint (b U)) := ⟨T, hp⟩
  rw [physicalMeshRecovery, dif_pos hex]
  obtain ⟨k, qU, qT, x, hvertices, hU, hT⟩ :=
    hb (Classical.choose hex) T p (Classical.choose_spec hex) hp
  exact affineBasisPhysicalSamplingRecovery_sharedSubface
    (b (Classical.choose hex)) (b T) qU qT hvertices n hn f x p hU hT

theorem physicalMeshRecovery_zero_of_not_mem
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (p : E) (hp : p ∉ physicalMeshSet b) :
    physicalMeshRecovery b n hn f p = 0 := by
  have hnot : ¬∃ T, p ∈ Set.range (physicalSimplexPoint (b T)) := by
    simpa only [physicalMeshSet, mem_iUnion] using hp
  simp only [physicalMeshRecovery, dif_neg hnot]

theorem physicalMeshRecovery_nonneg
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (hf : ∀ p ∈ physicalMeshSet b, 0 ≤ f p)
    (p : E) : 0 ≤ physicalMeshRecovery b n hn f p := by
  by_cases hp : p ∈ physicalMeshSet b
  · obtain ⟨T, x, hx⟩ := mem_iUnion.mp hp
    rw [physicalMeshRecovery_eq_on_element b hb n hn f T p ⟨x, hx⟩, ← hx,
      affineBasisPhysicalSamplingRecovery_eq]
    apply physicalSamplingRecovery_nonneg
    intro y
    exact hf _ (mem_iUnion.mpr ⟨T, y, rfl⟩)
  · rw [physicalMeshRecovery_zero_of_not_mem b n hn f p hp]

variable [Finite ι]

theorem isCompact_physicalMeshSet
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) : IsCompact (physicalMeshSet b) :=
  isCompact_iUnion fun T => isCompact_range_physicalSimplexPoint_affineBasis (b T)

/-- Closed finite-cover pasting of the actual element polynomials. -/
theorem continuousOn_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) :
    ContinuousOn (physicalMeshRecovery b n hn f) (physicalMeshSet b) := by
  apply (locallyFinite_of_finite (fun T => Set.range (physicalSimplexPoint (b T)))).continuousOn_iUnion
  · intro T
    exact isClosed_range_physicalSimplexPoint_affineBasis (b T)
  · intro T
    apply (contDiff_affineBasisPhysicalSamplingRecovery 1 (b T) n hn f).continuous.continuousOn.congr
    intro p hp
    exact physicalMeshRecovery_eq_on_element b hb n hn f T p hp

omit [Finite ι] in
/-- Boundary trace vanishes when a boundary point is represented on an actual
face and the input vanishes on the entire physical face. -/
theorem physicalMeshRecovery_zero_subface {k : ℕ}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (T : ι) (q : SimplexSubface k d)
    (hf : ∀ y : BarycentricPoint k,
      f (physicalSimplexPoint (q.vertices (fun i => b T i)) y) = 0)
    (x : BarycentricPoint k) :
    physicalMeshRecovery b n hn f (physicalSimplexPoint (b T) (q.point x)) = 0 := by
  rw [physicalMeshRecovery_eq_on_element b hb n hn f T _ ⟨q.point x, rfl⟩]
  exact affineBasisPhysicalSamplingRecovery_zero_subface q (b T) n hn f hf x

/-- The zero extension is genuinely continuous if its recovered boundary
trace is zero. This is not yet an H01 approximation theorem. -/
theorem continuous_physicalMeshRecovery_of_zero_frontier
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hzero : ∀ p ∈ frontier (physicalMeshSet b), physicalMeshRecovery b n hn f p = 0) :
    Continuous (physicalMeshRecovery b n hn f) := by
  let S := physicalMeshSet b
  have hS : IsClosed S := (isCompact_physicalMeshSet b).isClosed
  have houtside : ContinuousOn (physicalMeshRecovery b n hn f) (closure Sᶜ) := by
    apply continuousOn_const.congr
    intro p hp
    by_cases hpin : p ∈ S
    · apply hzero
      rw [frontier, hS.closure_eq]
      exact ⟨hpin, by simpa only [closure_compl, mem_compl_iff] using hp⟩
    · exact physicalMeshRecovery_zero_of_not_mem b n hn f p hpin
  have hcover : S ∪ closure Sᶜ = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ S
    · exact Or.inl hp
    · exact Or.inr (subset_closure hp)
  apply continuousOn_univ.mp
  rw [← hcover]
  exact (continuousOn_physicalMeshRecovery b hb n hn f).union_of_isClosed
    houtside hS isClosed_closure

theorem tsupport_physicalMeshRecovery_subset
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) (f : E → ℝ) :
    tsupport (physicalMeshRecovery b n hn f) ⊆ physicalMeshSet b := by
  apply closure_minimal _ (isCompact_physicalMeshSet b).isClosed
  intro p hp
  by_contra hnot
  exact (mem_support.mp hp) (physicalMeshRecovery_zero_of_not_mem b n hn f p hnot)

theorem hasCompactSupport_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) (f : E → ℝ) :
    HasCompactSupport (physicalMeshRecovery b n hn f) := by
  exact (isCompact_physicalMeshSet b).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_physicalMeshRecovery_subset b n hn f)

/-- The boundary is covered by physical subfaces lying entirely in the
boundary. This is geometric data, independent of the sampled function. -/
def physicalBoundaryFaces (b : ι → AffineBasis (Fin (d + 1)) ℝ E) : Prop :=
  ∀ p ∈ frontier (physicalMeshSet b),
    ∃ (T : ι) (k : ℕ) (q : SimplexSubface k d) (x : BarycentricPoint k),
      physicalSimplexPoint (b T) (q.point x) = p ∧
      Set.range (physicalSimplexPoint (q.vertices (fun i => b T i))) ⊆
        frontier (physicalMeshSet b)

omit [Finite ι] in
theorem physicalMeshRecovery_zero_frontier
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) :
    ∀ p ∈ frontier (physicalMeshSet b), physicalMeshRecovery b n hn f p = 0 := by
  intro p hp
  obtain ⟨T, k, q, x, hpoint, hface⟩ := hboundary p hp
  rw [← hpoint]
  exact physicalMeshRecovery_zero_subface b hb n hn f T q
    (fun y => hf _ (hface ⟨y, rfl⟩)) x

/-- Actual continuous zero extension, derived from geometric face matching
and zero input data on the physical boundary. -/
theorem continuous_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) :
    Continuous (physicalMeshRecovery b n hn f) :=
  continuous_physicalMeshRecovery_of_zero_frontier b hb n hn f
    (physicalMeshRecovery_zero_frontier b hb hboundary n hn f hf)

end

end BernsteinObstacle
