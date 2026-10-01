import BernsteinObstacle.SimplexAffineRecovery
import Mathlib.Analysis.Normed.Module.Basic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
An actual affine map from barycentric coordinates to physical vertices, with
a mesh-diameter bound and a local Lipschitz error estimate for Bernstein
sampling recovery. No shape-regularity or nondegeneracy is needed for this
C0 estimate. This is not the derivative or Sobolev H1 estimate.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def physicalSimplexPoint {d : ℕ} (v : Fin (d + 1) → E)
    (x : BarycentricPoint d) : E :=
  ∑ i, x.1 i • v i

theorem physicalSimplexPoint_sub {d : ℕ} (v : Fin (d + 1) → E)
    (x : BarycentricPoint d) (a : E) :
    physicalSimplexPoint v x - a = ∑ i, x.1 i • (v i - a) := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, x.2.2, one_smul]
  rfl

theorem norm_physicalSimplexPoint_sub_le {d : ℕ} (v : Fin (d + 1) → E)
    (x : BarycentricPoint d) (a : E) (h : ℝ)
    (hv : ∀ i, ‖v i - a‖ ≤ h) :
    ‖physicalSimplexPoint v x - a‖ ≤ h := by
  rw [physicalSimplexPoint_sub]
  calc
    ‖∑ i, x.1 i • (v i - a)‖ ≤ ∑ i, ‖x.1 i • (v i - a)‖ :=
      norm_sum_le _ _
    _ = ∑ i, x.1 i * ‖v i - a‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (x.2.1 i)]
    _ ≤ ∑ i, x.1 i * h := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hv i) (x.2.1 i)
    _ = h := by rw [← Finset.sum_mul, x.2.2, one_mul]

/-- Vertex diameter bounds every pair of points of the physical simplex. -/
theorem physicalSimplexPoint_diameter_le {d : ℕ} (v : Fin (d + 1) → E)
    (h : ℝ) (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (x y : BarycentricPoint d) :
    ‖physicalSimplexPoint v x - physicalSimplexPoint v y‖ ≤ h := by
  apply norm_physicalSimplexPoint_sub_le v x (physicalSimplexPoint v y) h
  intro i
  rw [norm_sub_rev]
  exact norm_physicalSimplexPoint_sub_le v y (v i) h (fun j => hv j i)

def physicalSamplingRecovery {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (x : BarycentricPoint d) : ℝ :=
  simplexSamplingRecovery d n hn (fun y => f (physicalSimplexPoint v y)) x

theorem physicalSamplingRecovery_nonneg {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ y : BarycentricPoint d, 0 ≤ f (physicalSimplexPoint v y))
    (x : BarycentricPoint d) :
    0 ≤ physicalSamplingRecovery v n hn f x := by
  exact simplexSamplingRecovery_nonneg d n hn
    (fun y => f (physicalSimplexPoint v y)) hf x

theorem physicalSamplingRecovery_const {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (c : ℝ) (x : BarycentricPoint d) :
    physicalSamplingRecovery v n hn (fun _ => c) x = c := by
  exact simplexSamplingRecovery_const d n hn c x

theorem physicalSamplingRecovery_affine {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ℓ : E →ₗ[ℝ] ℝ)
    (x : BarycentricPoint d) :
    physicalSamplingRecovery v n hn (fun p => a + ℓ p) x =
      a + ℓ (physicalSimplexPoint v x) := by
  simp only [physicalSamplingRecovery, physicalSimplexPoint, map_sum,
    map_smul, smul_eq_mul]
  simpa only [mul_comm] using
    simplexSamplingRecovery_affine d n hn a (fun i => ℓ (v i)) x

/-- A bounded Taylor remainder yields second-order C0 error. The remainder
estimate is an explicit hypothesis; no Hessian or Sobolev theorem is asserted. -/
theorem physicalSamplingRecovery_taylor_error_le {d : ℕ}
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (x : BarycentricPoint d) (ℓ : E →ₗ[ℝ] ℝ) (M h : ℝ)
    (hM : 0 ≤ M) (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (hf : ∀ y : BarycentricPoint d,
      |f (physicalSimplexPoint v y) -
        (f (physicalSimplexPoint v x) +
          ℓ (physicalSimplexPoint v y - physicalSimplexPoint v x))| ≤
        M * ‖physicalSimplexPoint v y - physicalSimplexPoint v x‖ ^ 2) :
    |physicalSamplingRecovery v n hn f x - f (physicalSimplexPoint v x)| ≤
      M * h ^ 2 := by
  have hh : 0 ≤ h := le_trans (norm_nonneg _) (hv 0 0)
  let q : E → ℝ := fun p =>
    (f (physicalSimplexPoint v x) - ℓ (physicalSimplexPoint v x)) + ℓ p
  have hq : physicalSamplingRecovery v n hn q x = f (physicalSimplexPoint v x) := by
    rw [physicalSamplingRecovery_affine]
    ring
  have hclose : ∀ y : BarycentricPoint d,
      |f (physicalSimplexPoint v y) - q (physicalSimplexPoint v y)| ≤ M * h ^ 2 := by
    intro y
    have hbound := physicalSimplexPoint_diameter_le v h hv y x
    calc
      |f (physicalSimplexPoint v y) - q (physicalSimplexPoint v y)| =
          |f (physicalSimplexPoint v y) -
            (f (physicalSimplexPoint v x) +
              ℓ (physicalSimplexPoint v y - physicalSimplexPoint v x))| := by
        dsimp [q]
        rw [map_sub]
        congr 1
        ring
      _ ≤ M * ‖physicalSimplexPoint v y - physicalSimplexPoint v x‖ ^ 2 := hf y
      _ ≤ M * h ^ 2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hh |>.2 hbound) hM
  have hs := simplexSamplingRecovery_abs_sub_le d n hn
    (fun y => f (physicalSimplexPoint v y))
    (fun y => q (physicalSimplexPoint v y)) (M * h ^ 2) hclose x
  change |physicalSamplingRecovery v n hn f x - physicalSamplingRecovery v n hn q x| ≤ _ at hs
  rwa [hq] at hs

/-- Uniform C0 error at most L times the physical vertex diameter. -/
theorem physicalSamplingRecovery_abs_error_le {d : ℕ} (v : Fin (d + 1) → E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (L h : ℝ)
    (hL : 0 ≤ L) (hv : ∀ i j, ‖v i - v j‖ ≤ h)
    (hf : ∀ x y : BarycentricPoint d,
      |f (physicalSimplexPoint v x) - f (physicalSimplexPoint v y)| ≤
        L * ‖physicalSimplexPoint v x - physicalSimplexPoint v y‖)
    (x : BarycentricPoint d) :
    |physicalSamplingRecovery v n hn f x - f (physicalSimplexPoint v x)| ≤ L * h := by
  apply simplexSamplingRecovery_abs_error_le d n hn
    (fun y => f (physicalSimplexPoint v y)) x (L * h)
  intro y
  exact le_trans (hf y x)
    (mul_le_mul_of_nonneg_left (physicalSimplexPoint_diameter_le v h hv y x) hL)

end

end BernsteinObstacle
