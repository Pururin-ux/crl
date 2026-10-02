import BernsteinObstacle.PhysicalGeometricShape

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

theorem norm_toLp_mul_of_ae_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q G : α → ℝ}
    (hq : AEStronglyMeasurable q μ) (hG : MemLp G 2 μ) (B : ℝ≥0)
    (hbound : ∀ᵐ x ∂μ, ‖q x‖ ≤ B) :
    ‖(memLp_mul_of_ae_bound hq hG B hbound).toLp (fun x => q x * G x)‖ ≤
      B * ‖hG.toLp G‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have hfin : ‖(B : ℝ)‖ₑ * eLpNorm G 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top enorm_ne_top hG.2.ne
  simpa only [ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg B.coe_nonneg] using
    ENNReal.toReal_mono hfin (eLpNorm_mul_le_of_ae_bound B hbound)

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual Poincare bound for a smooth interior test function in a coordinate
slab. Test integration by parts against x_i * phi, then use the actual L2
inner-product Cauchy-Schwarz inequality. The constant is 2R, not claimed
optimal; the only geometric bound is |x_i|<=R on Ω. -/
theorem poincare_physicalTestLp_of_coordinate_bound {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (φ : PhysicalSobolevTest Ω) :
    ‖physicalTestLp φ‖ ≤ (2 * (R : ℝ)) * ‖physicalTestDerivativeLp φ i‖ := by
  let μ := volume.restrict Ω
  let coord : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) i
  let D : E → ℝ := fun x => (fderiv ℝ φ.1 x) (EuclideanSpace.single i 1)
  let ψ : PhysicalSobolevTest Ω :=
    ⟨φ.1 * coord, φ.2.1.mul coord.contDiff, φ.2.2.1.mul_right,
      tsupport_mul_subset_left.trans φ.2.2.2⟩
  have hD (x : E) : (fderiv ℝ ψ.1 x) (EuclideanSpace.single i 1) =
      φ.1 x + coord x * D x := by
    have hd := ((φ.2.1.differentiable (by simp)) x).hasFDerivAt.mul coord.hasFDerivAt
    convert! congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd.fderiv using 1
    simp [D, coord, smul_eq_mul]
  have hu : MemLp φ.1 2 μ := (physicalTestH1Witness hΩ φ).memLp
  have hg : MemLp D 2 μ := by
    simpa only [physicalTestH1Witness, μ, D, gradient_component_eq_fderiv_apply] using
      (physicalTestH1Witness hΩ φ).weakGrad_component_memLp i
  have hcoord : AEStronglyMeasurable (fun x => coord x) μ := coord.continuous.aestronglyMeasurable
  have hcoordB : ∀ᵐ x ∂μ, ‖coord x‖ ≤ R := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hslab x hx
  have hV := memLp_mul_of_ae_bound hcoord hu R hcoordB
  have hW := memLp_mul_of_ae_bound hcoord hg R hcoordB
  let U : Lp ℝ 2 μ := hu.toLp φ.1
  let G : Lp ℝ 2 μ := hg.toLp D
  let V : Lp ℝ 2 μ := hV.toLp (fun x => coord x * φ.1 x)
  let W : Lp ℝ 2 μ := hW.toLp (fun x => coord x * D x)
  have hVbound : ‖V‖ ≤ (R : ℝ) * ‖U‖ := norm_toLp_mul_of_ae_bound hcoord hu R hcoordB
  have hcross : ⟪U, W⟫_ℝ = ⟪G, V⟫_ℝ := by
    rw [← integral_mul_eq_L2_inner hu hW, ← integral_mul_eq_L2_inner hg hV]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hweak := (hasWeakPartialDeriv_of_contDiff hΩ
    (φ.2.1.of_le (by simp)) (i := i)) ψ.1 ψ.2.1 ψ.2.2.1 ψ.2.2.2
  simp_rw [hD] at hweak
  have hweak' : ⟪U, U + W⟫_ℝ = -⟪G, V⟫_ℝ := by
    rw [← hu.toLp_add hW, ← integral_mul_eq_L2_inner hu (hu.add hW),
      ← integral_mul_eq_L2_inner hg hV]
    convert! hweak using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ψ, D, Pi.mul_apply]
    ring
  rw [inner_add_right, real_inner_self_eq_norm_sq, hcross] at hweak'
  have hcs : -⟪G, V⟫_ℝ ≤ (R : ℝ) * ‖U‖ * ‖G‖ := by
    calc
      -⟪G, V⟫_ℝ ≤ |⟪G, V⟫_ℝ| := neg_le_abs _
      _ ≤ ‖G‖ * ‖V‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖G‖ * ((R : ℝ) * ‖U‖) := mul_le_mul_of_nonneg_left hVbound (norm_nonneg _)
      _ = _ := by ring
  have hnorm : ‖U‖ ≤ (2 * (R : ℝ)) * ‖G‖ := by
    by_cases hU : ‖U‖ = 0
    · simp only [hU]
      positivity
    · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg U) (Ne.symm hU))).mp
      nlinarith [hweak', hcs]
  simpa only [U, G, physicalTestLp, physicalTestDerivativeLp,
    gradient_component_eq_fderiv_apply, D] using hnorm

variable [NeZero d]

/-- The actual H01 closure extends the smooth coordinate-slab Poincare
bound to every H01 Hilbert element, using actual joint L2 convergence. -/
theorem poincare_physicalH01_of_coordinate_bound {Ω : Set E} (hΩ : IsOpen Ω)
    (i : Fin d) (R : ℝ≥0) (hslab : ∀ x ∈ Ω, ‖x i‖ ≤ R)
    (z : physicalH01Submodule Ω hΩ) :
    ‖z.1.1 0‖ ≤ (2 * (R : ℝ)) * ‖z.1.1 i.succ‖ := by
  have hu := memH01_of_mem_physicalH01Submodule hΩ z.2
  rcases hu.2 with ⟨hw, φ, hφ, hc, hs, hf, hg⟩
  let ψ : ℕ → PhysicalSobolevTest Ω := fun n => ⟨φ n, hφ n, hc n, hs n⟩
  have hconv := (tendsto_physicalH1OfTest_iff hΩ ψ hw).mpr ⟨hf, hg⟩
  have heq : physicalH1OfWitness hw = z.1 :=
    (physicalH1OfWitness_independent hΩ hw (physicalH1Witness z.1)).trans
      (physicalH1OfWitness_canonical hΩ z.1)
  rw [heq] at hconv
  have hcomponents := (tendsto_physicalH1_iff_components _ _).mp hconv
  exact le_of_tendsto_of_tendsto
    ((hcomponents 0).norm) (((hcomponents i.succ).norm).const_mul (2 * (R : ℝ)))
    (Eventually.of_forall fun n => by
      simpa only [physicalH1OfTest, physicalH1OfWitness, physicalH1AmbientOfWitness,
        physicalTestH1Witness, physicalTestLp, physicalTestDerivativeLp,
        gradient_component_eq_fderiv_apply, Fin.cases_zero, Fin.cases_succ] using
        poincare_physicalTestLp_of_coordinate_bound hΩ i R hslab (ψ n))

end

end BernsteinObstacle
