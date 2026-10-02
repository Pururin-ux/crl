import BernsteinObstacle.PhysicalL2Dirichlet
import BernsteinObstacle.PhysicalConeConvex
import BernsteinObstacle.PhysicalCompactPoincare
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Existence is proved by a Cauchy minimizing sequence for the actual coercive
quadratic energy. The infimum/sequence/completeness structure adapts Mathlib's
`exists_norm_eq_iInf_of_complete_convex` (Projection/Minimal.lean, Apache-2.0;
Zhouhang Zhou, Frederic Dupuis, Heather Macbeth), replacing its norm
parallelogram identity with the symmetric quadratic-energy midpoint identity.
No weak compactness or assumed minimizer is used.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace BigOperators

namespace BernsteinObstacle

noncomputable section

def coerciveQuadraticEnergy {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ) (u : X) : ℝ :=
  (1 / 2 : ℝ) * B u u - F u

theorem coerciveQuadraticEnergy_lower_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u) (u : X) :
    -(C * ‖F‖ ^ 2) / 2 ≤ coerciveQuadraticEnergy B F u := by
  have hb := hbound u
  have hF : F u ≤ ‖F‖ * ‖u‖ := by
    calc
      F u ≤ |F u| := le_abs_self _
      _ ≤ ‖F‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using F.le_opNorm u
  have hCF := mul_le_mul_of_nonneg_left hF hC.le
  have hs := sq_nonneg (‖u‖ - C * ‖F‖)
  have hm : C * (-(C * ‖F‖ ^ 2) / 2) ≤ C * coerciveQuadraticEnergy B F u := by
    unfold coerciveQuadraticEnergy
    nlinarith
  exact (mul_le_mul_iff_right₀ hC).mp hm

theorem coerciveQuadraticEnergy_midpoint {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (u v : X) :
    coerciveQuadraticEnergy B F ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) =
      (1 / 2 : ℝ) * (coerciveQuadraticEnergy B F u + coerciveQuadraticEnergy B F v) -
        (1 / 8 : ℝ) * B (u - v) (u - v) := by
  have hs := hsymm u v
  simp only [coerciveQuadraticEnergy, map_add, map_smul, add_apply, smul_apply,
    map_sub, sub_apply, RingHom.id_apply, smul_eq_mul]
  nlinarith

/-- A genuine quadratic-energy minimizer exists on every nonempty complete
convex feasible set. The squared norm bound is actual coercivity; it is not
an assumed approximation or solution-existence statement. -/
theorem exists_coerciveQuadraticEnergy_minimizer {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u)
    (K : Set X) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    ∃ u ∈ K, ∀ v ∈ K, coerciveQuadraticEnergy B F u ≤ coerciveQuadraticEnergy B F v := by
  let J := coerciveQuadraticEnergy B F
  let δ := ⨅ z : K, J z
  let : Nonempty K := hne.to_subtype
  have hlower : BddBelow (Set.range (fun z : K => J z)) :=
    ⟨-(C * ‖F‖ ^ 2) / 2, Set.forall_mem_range.2 fun z =>
      coerciveQuadraticEnergy_lower_bound B F C hC hbound z⟩
  have hδ (z : K) : δ ≤ J z := ciInf_le hlower z
  have hδ' (z : X) (hz : z ∈ K) : δ ≤ J z := hδ ⟨z, hz⟩
  have hex (n : ℕ) : ∃ z : K, J z < δ + 1 / ((n : ℝ) + 1) :=
    exists_lt_of_ciInf_lt (lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat)
  let w : ℕ → K := fun n => Classical.choose (hex n)
  have hw (n : ℕ) : J (w n) < δ + 1 / ((n : ℝ) + 1) := Classical.choose_spec (hex n)
  have hJ : Tendsto (fun n => J (w n)) atTop (𝓝 δ) := by
    have hupper : Tendsto (fun n : ℕ => δ + 1 / ((n : ℝ) + 1)) atTop (𝓝 δ) := by
      convert! (tendsto_const_nhds (x := δ)).add tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [add_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => hδ (w n)) (fun n => (hw n).le)
  have hcauchy : CauchySeq (fun n => (w n : X)) := by
    apply cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt (8 * C * (1 / ((N : ℝ) + 1))))
    · intro p q N hp hq
      have hmid : (1 / 2 : ℝ) • (w p : X) + (1 / 2 : ℝ) • (w q : X) ∈ K :=
        hconvex (w p).2 (w q).2 (by norm_num) (by norm_num) (by norm_num)
      have hmidlower := hδ' _ hmid
      have hid := coerciveQuadraticEnergy_midpoint B F hsymm (w p) (w q)
      have hpJ : J (w p) ≤ δ + 1 / ((N : ℝ) + 1) :=
        (hw p).le.trans (add_le_add le_rfl (Nat.one_div_le_one_div hp))
      have hqJ : J (w q) ≤ δ + 1 / ((N : ℝ) + 1) :=
        (hw q).le.trans (add_le_add le_rfl (Nat.one_div_le_one_div hq))
      have hBd : B ((w p : X) - (w q : X)) ((w p : X) - (w q : X)) ≤
          8 * (1 / ((N : ℝ) + 1)) := by
        change J _ = _ at hid
        linarith
      have hs : ‖(w p : X) - (w q : X)‖ ^ 2 ≤ 8 * C * (1 / ((N : ℝ) + 1)) := by
        calc
          _ ≤ C * B ((w p : X) - (w q : X)) ((w p : X) - (w q : X)) := hbound _
          _ ≤ C * (8 * (1 / ((N : ℝ) + 1))) := mul_le_mul_of_nonneg_left hBd hC.le
          _ = _ := by ring
      rw [dist_eq_norm]
      calc
        _ = Real.sqrt (‖(w p : X) - (w q : X)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hs
    · have hc : Tendsto (fun x : ℝ => Real.sqrt (8 * C * x)) (𝓝 0) (𝓝 0) :=
        Continuous.tendsto' (by fun_prop) _ _ (by simp)
      exact hc.comp tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u, hu, hwu⟩ := cauchySeq_tendsto_of_isComplete hcomplete (fun n => (w n).2) hcauchy
  have hcont : Continuous J := continuous_quadratic_bilin_energy B F
  have heq : J u = δ := tendsto_nhds_unique (hcont.tendsto u |>.comp hwu) hJ
  exact ⟨u, hu, fun v hv => heq.le.trans (hδ' v hv)⟩

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Physical Poincare, actual completeness and the actual Dirichlet form
instantiate the minimizing-sequence theorem on a closed convex H01 set. -/
theorem exists_physicalDirichletMinimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ))
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    ∃ u, IsPhysicalDirichletMinimizer hΩ F K u := by
  exact @exists_coerciveQuadraticEnergy_minimizer (physicalH01Submodule (d := d) Ω hΩ)
    inferInstance (physicalH01RealNormedSpace (d := d) hΩ)
    (physicalDirichletBilin (d := d) hΩ) F (4 * (R : ℝ) ^ 2 + 1) (by positivity)
    (physicalDirichletBilin_coercivity_bound hΩ i R hslab)
    (physicalDirichletBilin_symmetric hΩ) K hne hclosed.isComplete hconvex

/-- Existence and uniqueness for the full actual nonnegative H01 obstacle
problem, with no supplied minimizer or positive-density oracle. -/
theorem existsUnique_physicalNonnegativeDirichletMinimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) :
    ∃! u, IsPhysicalDirichletMinimizer hΩ F (physicalNonnegativeH01Cone Ω hΩ) u := by
  obtain ⟨u, hu⟩ := exists_physicalDirichletMinimizer hΩ i R hslab F
    (physicalNonnegativeH01Cone Ω hΩ) ⟨0, zero_mem_physicalNonnegativeH01Cone hΩ⟩
    (isClosed_physicalNonnegativeH01Cone Ω hΩ) (convex_physicalNonnegativeH01Cone Ω hΩ)
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact physicalDirichletVI_unique hΩ i R hslab F _ v u
    (physicalDirichletMinimizer_is_VI hΩ F _ (convex_physicalNonnegativeH01Cone Ω hΩ) v hv)
    (physicalDirichletMinimizer_is_VI hΩ F _ (convex_physicalNonnegativeH01Cone Ω hΩ) u hu)

end

end BernsteinObstacle
