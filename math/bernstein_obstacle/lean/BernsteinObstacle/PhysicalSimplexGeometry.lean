import BernsteinObstacle.PhysicalSimplexCoordinates
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open scoped BigOperators
open MeasureTheory

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The physical simplex is exactly the nonnegative-coordinate region of a
genuine affine basis. -/
theorem range_physicalSimplexPoint_affineBasis {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) :
    Set.range (physicalSimplexPoint b) = {p | ∀ i, 0 ≤ b.coord i p} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩ i
    have hi := affineBasisCoordinate_physicalSimplexPoint b x i
    rw [affineBasisCoordinate_eq] at hi
    rw [hi]
    exact x.2.1 i
  · intro hp
    let x : BarycentricPoint d :=
      ⟨fun i => b.coord i p, hp, b.sum_coord_apply_eq_one p⟩
    exact ⟨x, b.linear_combination_coord_eq_self p⟩

/-- The physical element is compact, proved from its finite convex hull. -/
theorem isCompact_range_physicalSimplexPoint_affineBasis {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) :
    IsCompact (Set.range (physicalSimplexPoint b)) := by
  rw [range_physicalSimplexPoint_affineBasis, ← b.convexHull_eq_nonneg_coord]
  exact (Set.finite_range b).isCompact_convexHull (𝕜 := ℝ)

theorem isClosed_range_physicalSimplexPoint_affineBasis {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) :
    IsClosed (Set.range (physicalSimplexPoint b)) :=
  (isCompact_range_physicalSimplexPoint_affineBasis b).isClosed

/-- With the ordinary Borel measurable structure, the actual physical element
is measurable; this is not an extra mesh-measurability assumption. -/
theorem measurableSet_range_physicalSimplexPoint_affineBasis
    [MeasurableSpace E] [BorelSpace E] {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ E) :
    MeasurableSet (Set.range (physicalSimplexPoint b)) :=
  (isClosed_range_physicalSimplexPoint_affineBasis b).measurableSet

/-- The actual element has finite measure for any measure finite on compact
sets, in particular the ordinary volume measure on Euclidean space. -/
theorem measure_range_physicalSimplexPoint_affineBasis_lt_top
    [MeasurableSpace E] {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E)
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    μ (Set.range (physicalSimplexPoint b)) < ⊤ :=
  (isCompact_range_physicalSimplexPoint_affineBasis b).measure_lt_top

end

end BernsteinObstacle
