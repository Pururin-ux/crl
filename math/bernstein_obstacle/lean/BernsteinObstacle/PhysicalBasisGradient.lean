import BernsteinObstacle.PhysicalPolynomialDerivative

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-- The actual homogeneous Bernstein basis polynomial, before evaluation in
barycentric coordinates. Its degree is the sum of the entries of `α`. -/
def simplexBasisPolynomial (d : ℕ) (α : Fin (d + 1) → ℕ) :
    MvPolynomial (Fin (d + 1)) ℝ :=
  MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
    MvPolynomial.monomial (fullSimplexExponent d α) 1

theorem eval_simplexBasisPolynomial (d n : ℕ) (α : Fin (d + 1) → ℕ)
    (x : BarycentricPoint d) :
    MvPolynomial.eval x.1 (simplexBasisPolynomial d α) = simplexBasisNat d n α x := by
  simp [simplexBasisPolynomial, simplexBasisNat, eval_fullSimplexMonomial]

/-- A formal partial derivative of a Bernstein basis polynomial has nonnegative
value at every point with nonnegative barycentric coordinates, including faces. -/
theorem eval_pderiv_simplexBasisPolynomial_nonneg (d : ℕ)
    (α : Fin (d + 1) → ℕ) (j : Fin (d + 1)) (x : BarycentricPoint d) :
    0 ≤ MvPolynomial.eval x.1 (MvPolynomial.pderiv j (simplexBasisPolynomial d α)) := by
  classical
  simp only [simplexBasisPolynomial, MvPolynomial.pderiv_C_mul,
    map_mul, MvPolynomial.eval_C, MvPolynomial.pderiv_monomial,
    MvPolynomial.eval_monomial]
  apply mul_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg (fun i _ => pow_nonneg (x.2.1 i) _)

/-- The complete degree-`n` basis has partial-derivative mass exactly `n`.
This identity also holds at faces and for `n=0`. -/
theorem sum_eval_pderiv_simplexBasisPolynomial (d n : ℕ)
    (j : Fin (d + 1)) (x : BarycentricPoint d) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      MvPolynomial.eval x.1 (MvPolynomial.pderiv j (simplexBasisPolynomial d α))) =
      (n : ℝ) := by
  have hpoly := congrArg (MvPolynomial.pderiv j)
    (simplexMultinomialPolynomialExpansion d n)
  rw [pderiv_sum_X_pow] at hpoly
  have heval := congrArg (MvPolynomial.eval x.1) hpoly
  simpa [simplexBasisPolynomial, x.2.2] using heval.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Total operator-norm mass of actual physical basis derivatives, for affine
coordinates whose value at `p` is barycentric. Geometry enters through `ℓ`;
no inverse affine map or shape bound is silently assumed. -/
theorem sum_norm_fderiv_affineSimplexBasis_le (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (p : E) (x : BarycentricPoint d) (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      ‖fderiv ℝ (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
        (simplexBasisPolynomial d α)) p‖) ≤
      (n : ℝ) * ∑ i, ‖ℓ i‖ := by
  classical
  have hD (α : Fin (d + 1) → ℕ) :
      fderiv ℝ (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
        (simplexBasisPolynomial d α)) p =
        ∑ i, MvPolynomial.eval x.1
          (MvPolynomial.pderiv i (simplexBasisPolynomial d α)) • ℓ i := by
    rw [(hasFDerivAt_affinePhysicalPolynomial (simplexBasisPolynomial d α) a ℓ p).fderiv]
    simp_rw [hcoords]
  simp_rw [hD]
  calc
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        ‖∑ i, MvPolynomial.eval x.1
          (MvPolynomial.pderiv i (simplexBasisPolynomial d α)) • ℓ i‖) ≤
        ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
          ∑ i, MvPolynomial.eval x.1
            (MvPolynomial.pderiv i (simplexBasisPolynomial d α)) * ‖ℓ i‖ := by
      apply Finset.sum_le_sum
      intro α hα
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (eval_pderiv_simplexBasisPolynomial_nonneg d α i x)]
    _ = ∑ i, (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
          MvPolynomial.eval x.1
            (MvPolynomial.pderiv i (simplexBasisPolynomial d α))) * ‖ℓ i‖ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = (n : ℝ) * ∑ i, ‖ℓ i‖ := by
      simp_rw [sum_eval_pderiv_simplexBasisPolynomial]
      rw [Finset.mul_sum]

end

end BernsteinObstacle
