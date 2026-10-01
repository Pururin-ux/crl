import BernsteinObstacle.PhysicalMeshRecovery
import BernsteinObstacle.FiniteClosedLipschitzPasting

open scoped BigOperators NNReal
open Set

namespace BernsteinObstacle

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι] {d : ℕ}

/-- Actual derivative bounds on the convex physical elements give a global
Lipschitz bound for their continuous zero extension. Interfaces need not have
classical derivatives. -/
theorem lipschitzWith_physicalMeshRecovery_of_bound
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) (C : ℝ≥0)
    (hbound : ∀ T p, p ∈ Set.range (physicalSimplexPoint (b T)) →
      ‖fderiv ℝ (affineBasisPhysicalSamplingRecovery (b T) n hn f) p‖₊ ≤ C) :
    LipschitzWith C (physicalMeshRecovery b n hn f) := by
  let S := physicalMeshSet b
  have hS : IsClosed S := (isCompact_physicalMeshSet b).isClosed
  have hzero := physicalMeshRecovery_zero_frontier b hb hboundary n hn f hf
  have houtside : ∀ p ∈ closure Sᶜ, physicalMeshRecovery b n hn f p = 0 := by
    intro p hp
    by_cases hpin : p ∈ S
    · apply hzero
      rw [frontier, hS.closure_eq]
      exact ⟨hpin, by simpa only [closure_compl, mem_compl_iff] using hp⟩
    · exact physicalMeshRecovery_zero_of_not_mem b n hn f p hpin
  let cells : Option ι → Set E
    | none => closure Sᶜ
    | some T => Set.range (physicalSimplexPoint (b T))
  have hclosed : ∀ j, IsClosed (cells j) := by
    intro j
    cases j with
    | none => exact isClosed_closure
    | some T => exact isClosed_range_physicalSimplexPoint_affineBasis (b T)
  have hcover : ∀ p, ∃ j, p ∈ cells j := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨T, hT⟩ := mem_iUnion.mp hp
      exact ⟨some T, hT⟩
    · exact ⟨none, subset_closure hp⟩
  apply lipschitzWith_of_finite_closed_cover cells hclosed hcover C
  intro j
  cases j with
  | none =>
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    rw [houtside p hp, houtside q hq, dist_self]
    exact mul_nonneg C.2 dist_nonneg
  | some T =>
    have hdiff : Differentiable ℝ (affineBasisPhysicalSamplingRecovery (b T) n hn f) :=
      (contDiff_affineBasisPhysicalSamplingRecovery 1 (b T) n hn f).differentiable one_ne_zero
    have hlocal : LipschitzOnWith C
        (affineBasisPhysicalSamplingRecovery (b T) n hn f)
        (Set.range (physicalSimplexPoint (b T))) :=
      (convex_range_physicalSimplexPoint (b T)).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun p _ => hdiff p) (hbound T)
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    rw [physicalMeshRecovery_eq_on_element b hb n hn f T p hp,
      physicalMeshRecovery_eq_on_element b hb n hn f T q hq]
    exact hlocal.dist_le_mul p hp q hq

/-- A finite geometric conforming mesh with zero boundary data has an actual
globally Lipschitz recovered function. The finite constant is obtained from
continuous physical polynomial derivatives on compact elements. It is not
claimed to be uniform across a mesh family. -/
theorem exists_lipschitzWith_physicalMeshRecovery
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) :
    ∃ C : ℝ≥0, LipschitzWith C (physicalMeshRecovery b n hn f) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hbounds : ∀ T, ∃ C : ℝ≥0,
      ∀ p ∈ Set.range (physicalSimplexPoint (b T)),
        ‖fderiv ℝ (affineBasisPhysicalSamplingRecovery (b T) n hn f) p‖₊ ≤ C := by
    intro T
    have hcont : Continuous (fderiv ℝ (affineBasisPhysicalSamplingRecovery (b T) n hn f)) :=
      (contDiff_affineBasisPhysicalSamplingRecovery 1 (b T) n hn f).continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := (isCompact_range_physicalSimplexPoint_affineBasis (b T)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨⟨max C 0, le_max_right C 0⟩, ?_⟩
    intro p hp
    exact_mod_cast (hC p hp).trans (le_max_left C 0)
  choose K hK using hbounds
  refine ⟨∑ T, K T, lipschitzWith_physicalMeshRecovery_of_bound b hb hboundary n hn f hf _ ?_⟩
  intro T p hp
  exact (hK T p hp).trans (Finset.single_le_sum (fun U _ => (show 0 ≤ K U from zero_le)) (Finset.mem_univ T))

end

end BernsteinObstacle
