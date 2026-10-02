import BernsteinObstacle.PhysicalPositiveDensity

open MeasureTheory Set Function Filter Topology

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive smooth interior tests are dense in the actual full nonnegative
H01 Hilbert cone. This transports the proved raw-function/weak-gradient
density result through the proved Sobolev quotient realization. -/
theorem exists_positiveTest_strong_approximation {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH01Submodule Ω hΩ) (hz : z ∈ physicalNonnegativeH01Cone Ω hΩ) :
    ∃ ψ : ℕ → PhysicalSobolevTest Ω,
      (∀ n x, 0 ≤ (ψ n).1 x) ∧
      Tendsto (fun n => physicalH01OfTest hΩ (ψ n)) atTop (𝓝 z) := by
  have hu := memH01_of_mem_physicalH01Submodule hΩ z.2
  have hpos := (mem_physicalNonnegativeH01Cone_iff hΩ z).mp hz
  let D := physicalNonnegativeH01ApproximationWitness hΩ hu hpos
  let ψ : ℕ → PhysicalSobolevTest Ω := fun n =>
    ⟨D.approx n, D.smooth n, D.compactSupport n, D.support_subset n⟩
  refine ⟨ψ, D.nonnegative, ?_⟩
  apply tendsto_subtype_rng.mpr
  have heq : physicalH1OfWitness D.weakWitness = z.1 :=
    (physicalH1OfWitness_independent hΩ D.weakWitness (physicalH1Witness z.1)).trans
      (physicalH1OfWitness_canonical hΩ z.1)
  change Tendsto (fun n => physicalH1OfTest hΩ (ψ n)) atTop (𝓝 z.1)
  rw [← heq]
  exact (tendsto_physicalH1OfTest_iff hΩ ψ D.weakWitness).mpr
    ⟨D.function_tendsto, D.gradient_tendsto⟩

theorem physicalH01OfTest_mem_nonnegative {Ω : Set E} (hΩ : IsOpen Ω)
    (ψ : PhysicalSobolevTest Ω) (hpos : ∀ x, 0 ≤ ψ.1 x) :
    physicalH01OfTest hΩ ψ ∈ physicalNonnegativeH01Cone Ω hΩ :=
  (physicalH01OfWitness_mem_nonnegative_iff hΩ
    (physicalTestH1Witness hΩ ψ) (physicalTest_memH01 hΩ ψ)).mpr
      (Eventually.of_forall hpos)

end

end BernsteinObstacle
