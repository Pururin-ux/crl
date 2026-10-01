import BernsteinObstacle.PhysicalSimplexCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a multivariate polynomial preserves actual smoothness of
its coordinate functions. The statement covers every Mathlib smoothness order. -/
theorem contDiff_physicalPolynomial_eval (k : WithTop ENat) (q : MvPolynomial ι ℝ)
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ k (f i)) :
    ContDiff ℝ k (fun y => MvPolynomial.eval (fun i => f i y) q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const (c := a) : ContDiff ℝ k (fun _ : E => a))
  | add p q hp hq =>
      convert! hp.add hq using 1
      simp [map_add]
  | mul_X p j hp =>
      convert! hp.mul (hf j) using 1
      simp [map_mul, MvPolynomial.eval_X]

theorem contDiff_affinePhysicalPolynomial (k : WithTop ENat) (q : MvPolynomial ι ℝ)
    (a : ι → ℝ) (ℓ : ι → E →L[ℝ] ℝ) :
    ContDiff ℝ k (fun y => MvPolynomial.eval (fun i => a i + ℓ i y) q) := by
  apply contDiff_physicalPolynomial_eval
  intro i
  exact contDiff_const.add (ℓ i).contDiff

/-- The actual bounded-index physical field is globally smooth, regardless
of the signs of its coefficients. -/
theorem contDiff_affineSimplexField (k : WithTop ENat) (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (c : MultiIndex d n → ℝ) : ContDiff ℝ k (affineSimplexField d n a ℓ c) := by
  classical
  have h := ContDiff.sum (s := Finset.univ) (fun (α : MultiIndex d n) _ =>
    (contDiff_const (c := c α)).mul (contDiff_affinePhysicalPolynomial k
      (simplexBasisPolynomial d (fun i => (α.1 i : ℕ))) a ℓ))
  convert! h using 1

/-- Sampling need not assume a smooth input to give a smooth element
polynomial: its finitely many sampled values are constant coefficients. -/
theorem contDiff_affineBasisPhysicalSamplingRecovery [FiniteDimensional ℝ E]
    (k : WithTop ENat) {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) :
    ContDiff ℝ k (affineBasisPhysicalSamplingRecovery b n hn f) :=
  contDiff_affineSimplexField k d n
    (affineBasisCoordinateConstant b) (affineBasisCoordinateDerivative b) _

end

end BernsteinObstacle
