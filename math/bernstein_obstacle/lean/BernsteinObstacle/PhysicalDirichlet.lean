import BernsteinObstacle.PhysicalPoincare

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Explicit inherited real normed-space structure on the two nested
physical submodules. Its scalar action is the existing submodule action and
its norm bound is checked in the actual L2 product ambient space. -/
instance physicalH01RealNormedSpace {Ω : Set E} (hΩ : IsOpen Ω) :
    NormedSpace ℝ (physicalH01Submodule Ω hΩ) :=
  { (physicalH01Submodule Ω hΩ).module with
    norm_smul_le := fun r z => by
      change ‖r • (z.1.1 : PhysicalH1Ambient Ω)‖ ≤ ‖r‖ * ‖(z.1.1 : PhysicalH1Ambient Ω)‖
      exact norm_smul_le r (z.1.1 : PhysicalH1Ambient Ω) }

/-- Finite sums of pulled-back actual L2 inner products. A generic
construction keeps all continuous-linear-map space instances explicit. -/
def finiteComponentInnerBilin {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {ι : Type*} [Fintype ι]
    (p : ι → X →L[ℝ] Y) : X →L[ℝ] X →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ).bilinearComp (p i) (p i)

theorem affine_step_eq_combo {X : Type*} [AddCommGroup X] [Module ℝ X]
    (u v : X) (t : ℝ) : u + t • (v - u) = (1 - t) • u + t • v := by
  module

/-- Projection onto the function or one actual weak partial of an H01
element. Both zero-trace and weak-derivative graph inclusions are concrete. -/
def physicalH01Component {Ω : Set E} (hΩ : IsOpen Ω) (j : Fin (d + 1)) :
    physicalH01Submodule Ω hΩ →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (PiLp.proj 2 _ j).comp
    ((physicalH1Submodule Ω).subtypeL.comp (physicalH01Submodule Ω hΩ).subtypeL)

/-- The actual Dirichlet form on the concrete H01 space: the sum of
L2 inner products of weak partials, with no added reaction term. -/
def physicalDirichletBilin {Ω : Set E} (hΩ : IsOpen Ω) :
    physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ :=
  finiteComponentInnerBilin (X := physicalH01Submodule (d := d) Ω hΩ)
    (Y := Lp ℝ 2 (volume.restrict Ω)) (fun i : Fin d => physicalH01Component hΩ i.succ)

theorem physicalDirichletBilin_apply {Ω : Set E} (hΩ : IsOpen Ω)
    (z w : physicalH01Submodule Ω hΩ) :
    physicalDirichletBilin hΩ z w = ∑ i : Fin d, ⟪z.1.1 i.succ, w.1.1 i.succ⟫_ℝ := by
  simp [physicalDirichletBilin, finiteComponentInnerBilin, physicalH01Component]

theorem physicalDirichletBilin_symmetric {Ω : Set E} (hΩ : IsOpen Ω)
    (z w : physicalH01Submodule Ω hΩ) :
    physicalDirichletBilin hΩ z w = physicalDirichletBilin hΩ w z := by
  simp_rw [physicalDirichletBilin_apply, real_inner_comm]

theorem physicalDirichletBilin_self {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH01Submodule Ω hΩ) :
    physicalDirichletBilin hΩ z z = ∑ i : Fin d, ‖z.1.1 i.succ‖ ^ 2 := by
  simp_rw [physicalDirichletBilin_apply, real_inner_self_eq_norm_sq]

theorem physicalDirichletBilin_nonneg {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH01Submodule Ω hΩ) : 0 ≤ physicalDirichletBilin hΩ z z := by
  rw [physicalDirichletBilin_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Actual integral interpretation, with the canonical representatives of
the L2 weak partials. The finite sum and integrals are genuinely integrable. -/
theorem physicalDirichletBilin_eq_integral {Ω : Set E} (hΩ : IsOpen Ω)
    (z w : physicalH01Submodule Ω hΩ) :
    physicalDirichletBilin hΩ z w =
      ∫ x in Ω, ∑ i : Fin d, z.1.1 i.succ x * w.1.1 i.succ x := by
  rw [physicalDirichletBilin_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [Lp.toLp_coeFn] using
      (integral_mul_eq_L2_inner (Lp.memLp (z.1.1 i.succ))
        (Lp.memLp (w.1.1 i.succ))).symm
  · intro i _
    exact (Lp.memLp (z.1.1 i.succ)).integrable_mul (Lp.memLp (w.1.1 i.succ))

set_option maxHeartbeats 800000 in
/-- Poincare supplies an explicit lower bound for the genuine gradient-only
form in the actual full H01 norm. The coordinate-slab radius is the only
additional geometry; coercivity is a conclusion, not an input assumption. -/
theorem physicalDirichletBilin_coercivity_bound {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (z : physicalH01Submodule Ω hΩ) :
    ‖z‖ ^ 2 ≤ (4 * (R : ℝ) ^ 2 + 1) * physicalDirichletBilin hΩ z z := by
  have hp := poincare_physicalH01_of_coordinate_bound hΩ i R hslab z
  have hsq : ‖z.1.1 0‖ ^ 2 ≤ (2 * (R : ℝ) * ‖z.1.1 i.succ‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hp
  have hi : ‖z.1.1 i.succ‖ ^ 2 ≤ physicalDirichletBilin hΩ z z := by
    rw [physicalDirichletBilin_self]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z.1.1 j.succ‖) (Finset.mem_univ i)
  have hu : ‖z.1.1 0‖ ^ 2 ≤ 4 * (R : ℝ) ^ 2 * physicalDirichletBilin hΩ z z := by
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * (R : ℝ) ^ 2 by positivity)
    nlinarith [hsq, hh]
  rw [physicalH01_norm_sq hΩ, ← physicalDirichletBilin_self hΩ]
  nlinarith

theorem isCoercive_physicalDirichletBilin {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R) :
    @IsCoercive (physicalH01Submodule (d := d) Ω hΩ) inferInstance inferInstance
      (physicalDirichletBilin (d := d) hΩ) := by
  have hC : 0 < 4 * (R : ℝ) ^ 2 + 1 := by positivity
  refine ⟨(4 * (R : ℝ) ^ 2 + 1)⁻¹, inv_pos.mpr hC, ?_⟩
  intro z
  have hb := physicalDirichletBilin_coercivity_bound hΩ i R hslab z
  calc
    (4 * (R : ℝ) ^ 2 + 1)⁻¹ * ‖z‖ * ‖z‖ = ‖z‖ ^ 2 / (4 * (R : ℝ) ^ 2 + 1) := by ring
    _ ≤ physicalDirichletBilin hΩ z z :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hb)

/-- Physical load, energy, and obstacle VI use the actual Dirichlet form;
the load is any continuous linear functional on the constructed H01 space. -/
def physicalDirichletEnergy {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) (u : physicalH01Submodule Ω hΩ) : ℝ :=
  (1 / 2 : ℝ) * physicalDirichletBilin hΩ u u - F u

def IsPhysicalDirichletVISolution {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u : physicalH01Submodule Ω hΩ) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, F (v - u) ≤ physicalDirichletBilin hΩ u (v - u)

def IsPhysicalDirichletMinimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u : physicalH01Submodule Ω hΩ) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, physicalDirichletEnergy hΩ F u ≤ physicalDirichletEnergy hΩ F v

theorem physicalDirichletEnergy_difference {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) (u v : physicalH01Submodule Ω hΩ) :
    physicalDirichletEnergy hΩ F v - physicalDirichletEnergy hΩ F u =
      (1 / 2 : ℝ) * physicalDirichletBilin hΩ (v - u) (v - u) +
        physicalDirichletBilin hΩ u (v - u) - F (v - u) := by
  have hs := physicalDirichletBilin_symmetric hΩ v u
  simp only [physicalDirichletEnergy, map_sub, sub_apply] at *
  ring_nf at *
  linarith

theorem physicalDirichletVI_half_error_le_energy_gap {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u v : physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u) (hv : v ∈ K) :
    (1 / 2 : ℝ) * physicalDirichletBilin hΩ (v - u) (v - u) ≤
      physicalDirichletEnergy hΩ F v - physicalDirichletEnergy hΩ F u := by
  rw [physicalDirichletEnergy_difference]
  linarith [hu.2 v hv]

theorem physicalDirichletVI_is_minimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u : physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u) :
    IsPhysicalDirichletMinimizer hΩ F K u := by
  refine ⟨hu.1, fun v hv => ?_⟩
  have hg := physicalDirichletVI_half_error_le_energy_gap hΩ F K u v hu hv
  have hn := physicalDirichletBilin_nonneg hΩ (v - u)
  linarith

set_option maxHeartbeats 800000 in
/-- The converse uses feasible convex combinations and an explicit positive
step size in the quadratic energy identity, without postulating a first-order
optimality condition or assuming a differentiation theorem for the energy. -/
theorem physicalDirichletMinimizer_is_VI {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (hK : Convex ℝ K)
    (u : physicalH01Submodule Ω hΩ) (hu : IsPhysicalDirichletMinimizer hΩ F K u) :
    IsPhysicalDirichletVISolution hΩ F K u := by
  refine ⟨hu.1, fun v hv => ?_⟩
  by_contra h
  let δ : ℝ := F (v - u) - physicalDirichletBilin hΩ u (v - u)
  let A : ℝ := physicalDirichletBilin hΩ (v - u) (v - u)
  have hδ : 0 < δ := sub_pos.mpr (lt_of_not_ge h)
  have hA : 0 ≤ A := physicalDirichletBilin_nonneg hΩ (v - u)
  have hA1 : 0 < A + 1 := by linarith
  let t : ℝ := min 1 (δ / (A + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hδ hA1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htA : t * A ≤ δ := by
    have hh : t * (A + 1) ≤ δ := (le_div_iff₀ hA1).mp (min_le_right _ _)
    nlinarith
  have hfeas : u + t • (v - u) ∈ K := by
    have hc := hK hu.1 hv (show 0 ≤ 1 - t by linarith) ht.le (show (1 - t) + t = 1 by ring)
    have he := affine_step_eq_combo u v t
    rw [he]
    exact hc
  have hid : physicalDirichletEnergy hΩ F (u + t • (v - u)) - physicalDirichletEnergy hΩ F u =
      (1 / 2 : ℝ) * t ^ 2 * A - t * δ := by
    rw [physicalDirichletEnergy_difference hΩ F u (u + t • (v - u))]
    simp only [add_sub_cancel_left]
    simp only [map_smul, smul_apply, smul_eq_mul]
    dsimp only [A, δ]
    ring
  have hmin := hu.2 (u + t • (v - u)) hfeas
  have htd : t * (t * A) ≤ t * δ := mul_le_mul_of_nonneg_left htA ht.le
  have hpos := mul_pos ht hδ
  nlinarith [hid]

theorem physicalDirichletMinimizer_iff_VI {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (hK : Convex ℝ K)
    (u : physicalH01Submodule Ω hΩ) :
    IsPhysicalDirichletMinimizer hΩ F K u ↔ IsPhysicalDirichletVISolution hΩ F K u :=
  ⟨physicalDirichletMinimizer_is_VI hΩ F K hK u, physicalDirichletVI_is_minimizer hΩ F K u⟩

theorem physicalDirichletVI_unique {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u v : physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u)
    (hv : IsPhysicalDirichletVISolution hΩ F K v) : u = v := by
  have huv := hu.2 v hv.1
  have hvu := hv.2 u hu.1
  have hdiff : physicalDirichletBilin hΩ (v - u) (v - u) ≤ 0 := by
    simp only [map_sub, sub_apply] at *
    linarith
  have hb := physicalDirichletBilin_coercivity_bound hΩ i R hslab (v - u)
  have hz : ‖v - u‖ = 0 := by
    have hC : 0 ≤ 4 * (R : ℝ) ^ 2 + 1 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos hC hdiff
    nlinarith [norm_nonneg (v - u)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end

end BernsteinObstacle
