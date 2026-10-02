import BernsteinObstacle.PhysicalDirichlet

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

theorem continuous_quadratic_bilin_energy {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ) :
    Continuous (fun u : X => (1 / 2 : ℝ) * B u u - F u) :=
  (continuous_const.mul (B.continuous.clm_apply continuous_id)).sub F.continuous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual L2 forcing induces the continuous physical load by the function
coordinate of the concrete H01 space, without an assumed dual realization. -/
def physicalL2Load {Ω : Set E} (hΩ : IsOpen Ω) (f : Lp ℝ 2 (volume.restrict Ω)) :
    physicalH01Submodule Ω hΩ →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (physicalH01Component (d := d) hΩ 0)

theorem physicalL2Load_apply {Ω : Set E} (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume.restrict Ω)) (u : physicalH01Submodule Ω hΩ) :
    physicalL2Load hΩ f u = ⟪f, u.1.1 0⟫_ℝ := rfl

theorem physicalL2Load_eq_integral {Ω : Set E} (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume.restrict Ω)) (u : physicalH01Submodule Ω hΩ) :
    physicalL2Load hΩ f u = ∫ x in Ω, f x * u.1.1 0 x := by
  rw [physicalL2Load_apply]
  simpa only [Lp.toLp_coeFn] using
    (integral_mul_eq_L2_inner (Lp.memLp f) (Lp.memLp (u.1.1 0))).symm

theorem physicalL2DirichletEnergy_eq_integral {Ω : Set E} (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume.restrict Ω)) (u : physicalH01Submodule Ω hΩ) :
    physicalDirichletEnergy hΩ (physicalL2Load hΩ f) u =
      (1 / 2 : ℝ) * (∫ x in Ω, ∑ i : Fin d, u.1.1 i.succ x * u.1.1 i.succ x) -
        ∫ x in Ω, f x * u.1.1 0 x := by
  exact congrArg₂ (fun a b : ℝ => (1 / 2 : ℝ) * a - b)
    (physicalDirichletBilin_eq_integral hΩ u u) (physicalL2Load_eq_integral hΩ f u)

theorem continuous_physicalDirichletEnergy {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) :
    Continuous (physicalDirichletEnergy hΩ F) :=
  @continuous_quadratic_bilin_energy (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ)
    (physicalDirichletBilin (d := d) hΩ) F

theorem tendsto_physicalDirichletEnergy_of_strong {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ)
    (hconv : Tendsto uh atTop (𝓝 u)) :
    Tendsto (fun n => physicalDirichletEnergy hΩ F (uh n)) atTop
      (𝓝 (physicalDirichletEnergy hΩ F u)) :=
  (continuous_physicalDirichletEnergy hΩ F).tendsto u |>.comp hconv

end

end BernsteinObstacle
