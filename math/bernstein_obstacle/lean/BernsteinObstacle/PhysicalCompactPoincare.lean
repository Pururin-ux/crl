import BernsteinObstacle.PhysicalPoincare

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact containing set supplies the actual coordinate bound used in
Poincare, including the empty-domain case. No separately supplied bound is
needed when the physical domain lies in the finite compact mesh union. -/
theorem exists_coordinate_bound_of_compact {Ω S : Set E} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (i : Fin d) :
    ∃ R : ℝ≥0, ∀ x ∈ Ω, ‖x i‖ ≤ R := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (PiLp.continuous_apply 2 _ i).continuousOn
  refine ⟨⟨max B 0, le_max_right B 0⟩, fun x hx => ?_⟩
  exact (hB x (hΩS hx)).trans (le_max_left B 0)

theorem exists_coordinate_bound_of_physicalMeshSet {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) {Ω : Set E}
    (hcover : Ω ⊆ physicalMeshSet b) (i : Fin d) :
    ∃ R : ℝ≥0, ∀ x ∈ Ω, ‖x i‖ ≤ R :=
  exists_coordinate_bound_of_compact (isCompact_physicalMeshSet b) hcover i

end

end BernsteinObstacle
