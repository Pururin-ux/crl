import BernsteinObstacle.PhysicalDirichlet

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

def bilinContinuityConstant {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) : ℝ := ‖B‖

theorem bilinContinuityConstant_nonneg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) : 0 ≤ bilinContinuityConstant B := norm_nonneg B

theorem bilinContinuityConstant_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (u v : X) :
    ‖B u v‖ ≤ bilinContinuityConstant B * ‖u‖ * ‖v‖ := B.le_opNorm₂ u v

theorem linear_load_upper_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X →L[ℝ] ℝ) (u : X) : F u ≤ ‖F‖ * ‖u‖ := by
  calc
    F u ≤ |F u| := le_abs_self _
    _ ≤ ‖F‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using F.le_opNorm u

theorem linear_load_norm_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X →L[ℝ] ℝ) (u : X) : ‖F u‖ ≤ ‖F‖ * ‖u‖ := F.le_opNorm u

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def physicalDirichletContinuityConstant {Ω : Set E} (hΩ : IsOpen Ω) : ℝ :=
  @bilinContinuityConstant (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ)
    (physicalDirichletBilin (d := d) hΩ)

/-- The zero competitor and proved physical coercivity give a uniform
full-H01 bound for every actual Dirichlet obstacle VI solution. -/
theorem physicalDirichletVI_norm_bound {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (hzero : 0 ∈ K)
    (u : physicalH01Submodule Ω hΩ) (hu : IsPhysicalDirichletVISolution hΩ F K u) :
    ‖u‖ ≤ (4 * (R : ℝ) ^ 2 + 1) * ‖F‖ := by
  have hvi := hu.2 0 hzero
  simp only [zero_sub, map_neg] at hvi
  have hself : physicalDirichletBilin (d := d) hΩ u u ≤ F u := by linarith
  have hF : F u ≤ ‖F‖ * ‖u‖ :=
    @linear_load_upper_bound (physicalH01Submodule (d := d) Ω hΩ) inferInstance
      (physicalH01RealNormedSpace (d := d) hΩ) F u
  have hb := physicalDirichletBilin_coercivity_bound hΩ i R hslab u
  have hC : 0 ≤ 4 * (R : ℝ) ^ 2 + 1 := by positivity
  have hs : ‖u‖ ^ 2 ≤ ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) * ‖u‖ := by
    calc
      ‖u‖ ^ 2 ≤ (4 * (R : ℝ) ^ 2 + 1) * physicalDirichletBilin (d := d) hΩ u u := hb
      _ ≤ (4 * (R : ℝ) ^ 2 + 1) * (‖F‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (hself.trans hF) hC
      _ = _ := by ring
  by_cases hz : ‖u‖ = 0
  · simp only [hz]
    positivity
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz))).mp
    nlinarith [hs]

set_option maxHeartbeats 800000 in
/-- Inner approximation of the feasible set lets the continuous solution
test the discrete solution. Together with a recovery competitor this yields
an actual energy-error bound; no error closeness or weak compactness oracle
is assumed. This is a qualitative bound, not the sharp clipping estimate. -/
theorem physicalDirichletVI_inner_error_bound {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K Kh : Set (physicalH01Submodule Ω hΩ)) (hinner : Kh ⊆ K) (hzero : 0 ∈ Kh)
    (u uh v : physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u)
    (huh : IsPhysicalDirichletVISolution hΩ F Kh uh) (hv : v ∈ Kh) :
    ‖uh - u‖ ^ 2 ≤ (4 * (R : ℝ) ^ 2 + 1) *
      (physicalDirichletContinuityConstant hΩ * ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) + ‖F‖) * ‖v - u‖ := by
  have huc := hu.2 uh (hinner huh.1)
  have hud := huh.2 v hv
  have he : physicalDirichletBilin (d := d) hΩ (uh - u) (uh - u) ≤
      physicalDirichletBilin (d := d) hΩ uh (v - u) - F (v - u) := by
    simp only [map_sub, sub_apply] at huc hud ⊢
    linarith
  have hn := physicalDirichletVI_norm_bound hΩ i R hslab F Kh hzero uh huh
  have hupper : physicalDirichletBilin (d := d) hΩ uh (v - u) - F (v - u) ≤
      (physicalDirichletContinuityConstant hΩ * ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) + ‖F‖) * ‖v - u‖ := by
    calc
      physicalDirichletBilin (d := d) hΩ uh (v - u) - F (v - u) ≤
          ‖physicalDirichletBilin (d := d) hΩ uh (v - u)‖ + ‖F (v - u)‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        linarith [le_abs_self (physicalDirichletBilin (d := d) hΩ uh (v - u)), neg_le_abs (F (v - u))]
      _ ≤ physicalDirichletContinuityConstant hΩ * ‖uh‖ * ‖v - u‖ + ‖F‖ * ‖v - u‖ :=
        add_le_add
          (@bilinContinuityConstant_bound (physicalH01Submodule (d := d) Ω hΩ)
            inferInstance (physicalH01RealNormedSpace (d := d) hΩ)
            (physicalDirichletBilin (d := d) hΩ) uh (v - u))
          (@linear_load_norm_bound (physicalH01Submodule (d := d) Ω hΩ)
            inferInstance (physicalH01RealNormedSpace (d := d) hΩ) F (v - u))
      _ ≤ physicalDirichletContinuityConstant hΩ * ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) * ‖v - u‖ +
          ‖F‖ * ‖v - u‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn
              (@bilinContinuityConstant_nonneg (physicalH01Submodule (d := d) Ω hΩ)
                inferInstance (physicalH01RealNormedSpace (d := d) hΩ)
                (physicalDirichletBilin (d := d) hΩ))) (norm_nonneg _))
          (le_refl _)
      _ = _ := by ring
  have hb := physicalDirichletBilin_coercivity_bound hΩ i R hslab (uh - u)
  have hC : 0 ≤ 4 * (R : ℝ) ^ 2 + 1 := by positivity
  calc
    ‖uh - u‖ ^ 2 ≤ (4 * (R : ℝ) ^ 2 + 1) * physicalDirichletBilin (d := d) hΩ (uh - u) (uh - u) := hb
    _ ≤ (4 * (R : ℝ) ^ 2 + 1) *
        ((physicalDirichletContinuityConstant hΩ * ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) + ‖F‖) * ‖v - u‖) :=
      mul_le_mul_of_nonneg_left (he.trans hupper) hC
    _ = _ := by ring

/-- Strong convergence of actual physical VI solutions follows from inner
cones, a zero competitor, and strong recovery. Existence of those solutions
is explicitly not claimed by this theorem. -/
theorem tendsto_physicalDirichletVI_of_inner_recovery {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (Kh : ℕ → Set (physicalH01Submodule Ω hΩ))
    (hinner : ∀ n, Kh n ⊆ K) (hzero : ∀ n, 0 ∈ Kh n)
    (u : physicalH01Submodule Ω hΩ) (uh v : ℕ → physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u)
    (huh : ∀ n, IsPhysicalDirichletVISolution hΩ F (Kh n) (uh n))
    (hv : ∀ n, v n ∈ Kh n) (hconv : Tendsto v atTop (𝓝 u)) :
    Tendsto uh atTop (𝓝 u) := by
  let C : ℝ := (4 * (R : ℝ) ^ 2 + 1) *
    (physicalDirichletContinuityConstant hΩ * ((4 * (R : ℝ) ^ 2 + 1) * ‖F‖) + ‖F‖)
  have herr (n : ℕ) : ‖uh n - u‖ ^ 2 ≤ C * ‖v n - u‖ :=
    physicalDirichletVI_inner_error_bound hΩ i R hslab F K (Kh n) (hinner n) (hzero n)
      u (uh n) (v n) hu (huh n) (hv n)
  have hvnorm : Tendsto (fun n => ‖v n - u‖) atTop (𝓝 0) := by
    convert! (hconv.sub_const u).norm using 1 <;> simp only [sub_self, norm_zero]
  have hs : Tendsto (fun n => ‖uh n - u‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) herr (by simpa using hvnorm.const_mul C)
  have hnorm := Real.continuous_sqrt.tendsto 0 |>.comp hs
  have hnorm' : Tendsto (fun n => ‖uh n - u‖) atTop (𝓝 0) := by
    convert! hnorm using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_zero]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

/-- The actual physical Mosco theorem supplies the recovery automatically.
The output is strong full-H01 convergence and genuine energy minimality;
the theorem keeps solution existence as a separate explicit obligation. -/
theorem physicalDirichletVI_convergence_of_inner_mosco {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (Kh : ℕ → Set (physicalH01Submodule Ω hΩ))
    (hinner : ∀ n, Kh n ⊆ K) (hzero : ∀ n, 0 ∈ Kh n) (hM : MoscoConverges Kh K)
    (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ)
    (hu : IsPhysicalDirichletVISolution hΩ F K u)
    (huh : ∀ n, IsPhysicalDirichletVISolution hΩ F (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) ∧ IsPhysicalDirichletMinimizer hΩ F K u ∧
      ∀ n, IsPhysicalDirichletMinimizer hΩ F (Kh n) (uh n) := by
  obtain ⟨v, hv, hconv⟩ := hM.recovery u hu.1
  exact ⟨tendsto_physicalDirichletVI_of_inner_recovery hΩ i R hslab F K Kh hinner hzero
    u uh v hu huh hv hconv, physicalDirichletVI_is_minimizer hΩ F K u hu,
      fun n => physicalDirichletVI_is_minimizer hΩ F (Kh n) (uh n) (huh n)⟩

end

end BernsteinObstacle
