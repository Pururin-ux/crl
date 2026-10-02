import BernsteinObstacle.PhysicalConeClosed
import BernsteinObstacle.PhysicalBernsteinMinimizers

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual discrete Bernstein gradient-energy problem has exactly one
minimizer. Nonemptiness, closedness, convexity, completeness and coercivity
are all proved; no discrete minimizer or closedness witness is supplied. -/
theorem existsUnique_physicalBernsteinDirichletMinimizer {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) (hcover : Ω ⊆ physicalMeshSet b)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) :
    ∃! u, IsPhysicalDirichletMinimizer hΩ F (physicalBernsteinH01Cone b n Ω hΩ) u := by
  obtain ⟨R, hslab⟩ := exists_coordinate_bound_of_physicalMeshSet b hcover (0 : Fin d)
  obtain ⟨u, hu⟩ := exists_physicalDirichletMinimizer hΩ 0 R hslab F
    (physicalBernsteinH01Cone b n Ω hΩ) ⟨0, zero_mem_physicalBernsteinH01Cone b n hΩ⟩
    (isClosed_physicalBernsteinH01Cone b n hΩ) (convex_physicalBernsteinH01Cone b n hΩ)
  exact ⟨u, hu, fun v hv => physicalBernsteinMinimizer_unique b n hΩ hcover F v u hv hu⟩

theorem existsUnique_physicalNonnegativeDirichletMinimizer_of_compact
    {S Ω : Set E} (hS : IsCompact S) (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) :
    ∃! u, IsPhysicalDirichletMinimizer hΩ F (physicalNonnegativeH01Cone Ω hΩ) u := by
  obtain ⟨R, hslab⟩ := exists_coordinate_bound_of_compact hS hΩS (0 : Fin d)
  exact existsUnique_physicalNonnegativeDirichletMinimizer hΩ 0 R hslab F

/-- Construct continuous and discrete actual Bernstein obstacle minimizers
and prove strong H01 and energy convergence on a supplied geometric family.
No minimizer-existence input remains. Standard assembled-DOF identification,
construction of a particular mesh family and a sharp clipping rate are not
claimed by this theorem. -/
theorem exists_convergent_physicalBernsteinMinimizers_of_inscribed_balls
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n)
    (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (c : ∀ m, κ m → E) (r : ∀ m, κ m → ℝ) (hr : ∀ m T, 0 < r m T)
    (hball : ∀ m T, Metric.closedBall (c m T) (r m T) ⊆ Set.range (physicalSimplexPoint (b m T)))
    (σ : ℝ) (hσ : 0 ≤ σ) (hshape : ∀ m T, h m T / r m T ≤ σ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) :
    ∃ (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ),
      IsPhysicalDirichletMinimizer hΩ F (physicalNonnegativeH01Cone Ω hΩ) u ∧
      (∀ m, IsPhysicalDirichletMinimizer hΩ F (physicalBernsteinH01Cone (b m) n Ω hΩ) (uh m)) ∧
      Tendsto uh atTop (𝓝 u) ∧
      Tendsto (fun m => physicalDirichletEnergy hΩ F (uh m)) atTop
        (𝓝 (physicalDirichletEnergy hΩ F u)) := by
  have hSc : IsCompact S := by
    rw [← hsets 0]
    exact isCompact_physicalMeshSet (b 0)
  obtain ⟨u, hu, _hunique⟩ := existsUnique_physicalNonnegativeDirichletMinimizer_of_compact
    hSc hΩ (hΩS.trans interior_subset) F
  have hcover (m : ℕ) : Ω ⊆ physicalMeshSet (b m) := by
    simpa only [hsets m] using hΩS.trans interior_subset
  have hex (m : ℕ) : ∃ v, IsPhysicalDirichletMinimizer hΩ F
      (physicalBernsteinH01Cone (b m) n Ω hΩ) v :=
    (existsUnique_physicalBernsteinDirichletMinimizer (b m) n hΩ (hcover m) F).exists
  choose uh huh using hex
  have hconv := tendsto_physicalBernsteinMinimizers_of_inscribed_balls b hb hboundary S hsets
    hΩ hΩS n hn H hsmall h hdiam hmax c r hr hball σ hσ hshape F u uh hu huh
  exact ⟨u, uh, hu, huh, hconv, tendsto_physicalDirichletEnergy_of_strong hΩ F u uh hconv⟩

end

end BernsteinObstacle
