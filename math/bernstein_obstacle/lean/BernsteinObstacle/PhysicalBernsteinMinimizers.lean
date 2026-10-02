import BernsteinObstacle.PhysicalDirichletConvergence
import BernsteinObstacle.PhysicalConeConvex
import BernsteinObstacle.PhysicalCompactPoincare

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual symmetric Dirichlet energy minimizers on inner convex cones
converge strongly when the cones have Mosco recovery. The VI conditions are
derived from energy minimality, rather than independently assumed. -/
theorem tendsto_physicalDirichletMinimizers_of_inner_mosco {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (Kh : ℕ → Set (physicalH01Submodule Ω hΩ))
    (hK : Convex ℝ K) (hKh : ∀ n, Convex ℝ (Kh n))
    (hinner : ∀ n, Kh n ⊆ K) (hzero : ∀ n, 0 ∈ Kh n) (hM : MoscoConverges Kh K)
    (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletMinimizer hΩ F K u)
    (huh : ∀ n, IsPhysicalDirichletMinimizer hΩ F (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) :=
  (physicalDirichletVI_convergence_of_inner_mosco hΩ i R hslab F K Kh hinner hzero hM u uh
    (physicalDirichletMinimizer_is_VI hΩ F K hK u hu)
    (fun n => physicalDirichletMinimizer_is_VI hΩ F (Kh n) (hKh n) (uh n) (huh n))).1

/-- Strong convergence of actual gradient-energy Bernstein obstacle
minimizers on supplied conforming, shrinking, shape-regular physical meshes.
Positive H01 density, weak closure, geometric coordinate bounds, Poincare
coercivity, diagonal recovery, cone convexity, and VI optimality are all
proved upstream. The actual minimizers are supplied; their existence and the
equivalence to a particular assembled finite-DOF presentation remain separate
obligations. This theorem gives no high-order clipping rate. -/
theorem tendsto_physicalBernsteinMinimizers_of_inscribed_balls
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
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletMinimizer hΩ F (physicalNonnegativeH01Cone Ω hΩ) u)
    (huh : ∀ m, IsPhysicalDirichletMinimizer hΩ F (physicalBernsteinH01Cone (b m) n Ω hΩ) (uh m)) :
    Tendsto uh atTop (𝓝 u) := by
  have hSc : IsCompact S := by
    rw [← hsets 0]
    exact isCompact_physicalMeshSet (b 0)
  obtain ⟨R, hslab⟩ := exists_coordinate_bound_of_compact hSc (hΩS.trans interior_subset) (0 : Fin d)
  apply tendsto_physicalDirichletMinimizers_of_inner_mosco hΩ 0 R hslab F
    (physicalNonnegativeH01Cone Ω hΩ) (fun m => physicalBernsteinH01Cone (b m) n Ω hΩ)
    (convex_physicalNonnegativeH01Cone Ω hΩ)
    (fun m => convex_physicalBernsteinH01Cone (b m) n hΩ) _
    (fun m => zero_mem_physicalBernsteinH01Cone (b m) n hΩ) _ u uh hu huh
  · intro m
    apply physicalBernsteinH01Cone_subset_nonnegative (b m) n hΩ
    simpa only [hsets m] using hΩS.trans interior_subset
  · exact mosco_physicalBernsteinH01Cone_of_inscribed_balls b hb hboundary S hsets hΩ hΩS n hn
      H hsmall h hdiam hmax c r hr hball σ hσ hshape

/-- Uniqueness of genuine Bernstein gradient-energy minimizers follows from
the compact actual mesh, proved Poincare coercivity, and proved convexity. -/
theorem physicalBernsteinMinimizer_unique {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) (hcover : Ω ⊆ physicalMeshSet b)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (u v : physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletMinimizer hΩ F (physicalBernsteinH01Cone b n Ω hΩ) u)
    (hv : IsPhysicalDirichletMinimizer hΩ F (physicalBernsteinH01Cone b n Ω hΩ) v) : u = v := by
  obtain ⟨R, hslab⟩ := exists_coordinate_bound_of_physicalMeshSet b hcover (0 : Fin d)
  exact physicalDirichletVI_unique hΩ 0 R hslab F (physicalBernsteinH01Cone b n Ω hΩ) u v
    (physicalDirichletMinimizer_is_VI hΩ F _ (convex_physicalBernsteinH01Cone b n hΩ) u hu)
    (physicalDirichletMinimizer_is_VI hΩ F _ (convex_physicalBernsteinH01Cone b n hΩ) v hv)

end

end BernsteinObstacle
