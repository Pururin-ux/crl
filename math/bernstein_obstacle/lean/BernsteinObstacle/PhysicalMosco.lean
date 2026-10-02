import BernsteinObstacle.PhysicalDiscreteCone
import BernsteinObstacle.ScheduledRecovery

open MeasureTheory Set Function Filter Topology

namespace BernsteinObstacle

noncomputable section

/-- Diagonal recovery from actual row limits. Mesh thresholds and the stage
map are extracted internally. An arbitrary initial approximation is allowed:
the norm bound is needed only eventually, not at the artificial stage zero. -/
theorem exists_strong_diagonal_of_row_limits
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : ℕ → Set X) (w : ℕ → X) (R : ℕ → ℕ → X) (x : X)
    (hw : Tendsto w atTop (𝓝 x)) (hmem : ∀ m n, R m n ∈ K n)
    (hrow : ∀ m, Tendsto (R m) atTop (𝓝 (w m))) :
    ∃ u : ℕ → X, (∀ n, u n ∈ K n) ∧ Tendsto u atTop (𝓝 x) := by
  classical
  have hevent (m : ℕ) : ∀ᶠ n in atTop, ‖R m n - w m‖ ≤ physicalSmoothingScale m := by
    have hn : Tendsto (fun n => ‖R m n - w m‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using ((hrow m).sub_const (w m)).norm
    exact (hn.eventually_lt_const (physicalSmoothingScale_pos m)).mono fun _ h => h.le
  choose N hN using fun m => eventually_atTop.mp (hevent m)
  let threshold : ℕ → ℕ := fun m => max m (N m)
  have hself : ∀ m, m ≤ threshold m := fun m => le_max_left _ _
  let stage : ℕ → ℕ := scheduledStage threshold
  have hstage : Tendsto stage atTop atTop := scheduledStage_tendsto_atTop threshold hself
  have hbound : ∀ᶠ n in atTop,
      ‖R (stage n) n - w (stage n)‖ ≤ physicalSmoothingScale (stage n) := by
    filter_upwards [eventually_ge_atTop (threshold 0)] with n hn
    have hspec : threshold (stage n) ≤ n := by
      exact Nat.findGreatest_spec (P := fun m => threshold m ≤ n) (m := 0)
        (Nat.zero_le n) hn
    exact hN (stage n) n ((le_max_right _ _).trans hspec)
  have herr : Tendsto (fun n => ‖R (stage n) n - w (stage n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
    exact tendsto_physicalSmoothingScale.comp hstage
  refine ⟨fun n => R (stage n) n, fun n => hmem (stage n) n, ?_⟩
  exact diagonalRecovery_stronglyConverges w R stage x
    (fun n => ‖R (stage n) n - w (stage n)‖) hw hstage (fun _ => le_refl _) herr

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Mosco convergence of the actual physical Bernstein coefficient cones
to the full nonnegative H01 cone on a supplied changing affine mesh family.
Positive smooth density, Hilbert realization, discrete membership, actual
Bernstein recovery, diagonal scheduling, and weak closure are proved and
connected. The remaining geometric inputs are stated explicitly: finite
conforming cells with a common mesh set, geometric boundary cover, uniform
local coordinate shape control, and shrinking maximum size. No recovery,
positive-density, diagonal-threshold or Sobolev-faithfulness witness is an
assumption. This does not construct the conventional mesh family or prove
the gradient-energy/minimizer or high-order clipping-rate result. -/
theorem mosco_physicalBernsteinH01Cone
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n)
    (C : ℝ) (hC : 0 ≤ C) (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (hshape : ∀ m T, h m T * ∑ i, ‖affineBasisCoordinateDerivative (b m T) i‖ ≤ C) :
    MoscoConverges (fun m => physicalBernsteinH01Cone (b m) n Ω hΩ)
      (physicalNonnegativeH01Cone Ω hΩ) := by
  let K : ℕ → Set (physicalH01Submodule Ω hΩ) :=
    fun m => physicalBernsteinH01Cone (b m) n Ω hΩ
  apply mosco_of_recovery_of_subset_of_closedConvex K (physicalNonnegativeH01Cone Ω hΩ)
  · intro z hz
    obtain ⟨ψ, hψ, hconv⟩ := exists_positiveTest_strong_approximation hΩ z hz
    let R : ℕ → ℕ → physicalH01Submodule Ω hΩ := fun k m =>
      physicalSupportedMeshH01Recovery (b m) (hb m) (hboundary m) n hn (ψ k).1
        (zero_frontier_of_tsupport_subset_interior (b m)
          (by simpa only [hsets m] using (ψ k).2.2.2.trans hΩS)) hΩ
    have hmem (k m : ℕ) : R k m ∈ K m :=
      physicalSupportedMeshH01Recovery_mem_coefficientCone (b m) (hb m) (hboundary m)
        n hn (ψ k).1 _ hΩ (fun x _ => hψ k x)
    have hrow (k : ℕ) : Tendsto (R k) atTop (𝓝 (physicalH01OfTest hΩ (ψ k))) :=
      tendsto_physicalSupportedMeshH01Recovery b hb hboundary S hsets hΩ hΩS n hn (ψ k)
        C hC H hsmall h hdiam hmax hshape
    exact exists_strong_diagonal_of_row_limits K
      (fun k => physicalH01OfTest hΩ (ψ k)) R z hconv hmem hrow
  · intro m
    apply physicalBernsteinH01Cone_subset_nonnegative (b m) n hΩ
    simpa only [hsets m] using hΩS.trans interior_subset
  · exact convex_physicalNonnegativeH01Cone Ω hΩ
  · exact isClosed_physicalNonnegativeH01Cone Ω hΩ

end

end BernsteinObstacle
