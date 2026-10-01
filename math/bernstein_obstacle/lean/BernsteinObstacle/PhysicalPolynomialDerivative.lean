import BernsteinObstacle.PhysicalSimplexCalculus
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a multivariate polynomial along differentiable coordinate
functions has the actual Frechet derivative given by its formal partials. -/
theorem hasFDerivAt_physicalPolynomial_eval (q : MvPolynomial ι ℝ)
    (f : ι → E → ℝ) (f' : ι → E →L[ℝ] ℝ) (x : E)
    (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun y => MvPolynomial.eval (fun i => f i y) q)
      (∑ i, MvPolynomial.eval (fun j => f j x) (MvPolynomial.pderiv i q) • f' i) x := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a =>
      simpa [MvPolynomial.pderiv_C] using (hasFDerivAt_const (𝕜 := ℝ) a x)
  | add p q hp hq =>
      convert! hp.add hq using 1 <;>
        simp [map_add, add_smul, Finset.sum_add_distrib]
      all_goals rfl
  | mul_X p j hp =>
      have hder :
          (∑ i, MvPolynomial.eval (fun k => f k x) (MvPolynomial.pderiv i (p * MvPolynomial.X j)) • f' i) =
            f j x • (∑ i, MvPolynomial.eval (fun k => f k x) (MvPolynomial.pderiv i p) • f' i) +
              MvPolynomial.eval (fun k => f k x) p • f' j := by
        simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X, add_smul]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [smul_smul]
          congr 1
          ring
        · rw [Finset.sum_eq_single j]
          · simp
          · intro i hi hij
            simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
          · intro hnot
            exact (hnot (Finset.mem_univ j)).elim
      rw [hder]
      convert! hp.mul (hf j) using 1 <;>
        simp [map_mul, MvPolynomial.eval_X, add_comm]
      all_goals rfl

theorem fderiv_physicalPolynomial_eval (q : MvPolynomial ι ℝ)
    (f : ι → E → ℝ) (f' : ι → E →L[ℝ] ℝ) (x : E)
    (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    fderiv ℝ (fun y => MvPolynomial.eval (fun i => f i y) q) x =
      ∑ i, MvPolynomial.eval (fun j => f j x) (MvPolynomial.pderiv i q) • f' i :=
  (hasFDerivAt_physicalPolynomial_eval q f f' x hf).fderiv

/-- In affine physical coordinates the coordinate derivatives are actual
continuous linear maps, with no assumed polynomial-derivative oracle. -/
theorem hasFDerivAt_affinePhysicalPolynomial (q : MvPolynomial ι ℝ)
    (a : ι → ℝ) (ℓ : ι → E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y => MvPolynomial.eval (fun i => a i + ℓ i y) q)
      (∑ i, MvPolynomial.eval (fun j => a j + ℓ j x) (MvPolynomial.pderiv i q) • ℓ i) x := by
  apply hasFDerivAt_physicalPolynomial_eval
  intro i
  exact (ℓ i).hasFDerivAt.const_add (a i)

end

end BernsteinObstacle
