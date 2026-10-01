import BernsteinObstacle.PhysicalBasisGradient

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bounded-index Bernstein field evaluated as a function on the actual
physical vector space through affine coordinates. -/
def affineSimplexField (d n : ℕ) (a : Fin (d + 1) → ℝ)
    (ℓ : Fin (d + 1) → E →L[ℝ] ℝ) (c : MultiIndex d n → ℝ) (p : E) : ℝ :=
  ∑ α, c α * MvPolynomial.eval (fun i => a i + ℓ i p)
    (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))

/-- This physical function is exactly the upstream field at barycentric
coordinate values; it is not a replacement sampling operator. -/
theorem affineSimplexField_eq_simplexField (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (c : MultiIndex d n → ℝ) (p : E) (x : BarycentricPoint d)
    (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    affineSimplexField d n a ℓ c p = simplexField d n c x := by
  simp_rw [affineSimplexField, hcoords, eval_simplexBasisPolynomial d n,
    ← simplexBasis_eq_simplexBasisNat]
  rfl

theorem hasFDerivAt_affineSimplexField (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (c : MultiIndex d n → ℝ) (p : E) :
    HasFDerivAt (affineSimplexField d n a ℓ c)
      (∑ α : MultiIndex d n, c α • fderiv ℝ
        (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
          (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p) p := by
  classical
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun (α : MultiIndex d n) _ =>
      (hasFDerivAt_affinePhysicalPolynomial
        (simplexBasisPolynomial d (fun i => (α.1 i : ℕ))) a ℓ p).differentiableAt.hasFDerivAt.const_mul
        (c α))
  convert! h using 1

theorem fderiv_affineSimplexField (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (c : MultiIndex d n → ℝ) (p : E) :
    fderiv ℝ (affineSimplexField d n a ℓ c) p =
      ∑ α : MultiIndex d n, c α • fderiv ℝ
        (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
          (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p :=
  (hasFDerivAt_affineSimplexField d n a ℓ c p).fderiv

theorem sum_norm_fderiv_affineSimplexBasis_multiIndex_le (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (p : E) (x : BarycentricPoint d) (hcoords : ∀ i, a i + ℓ i p = x.1 i) :
    (∑ α : MultiIndex d n, ‖fderiv ℝ
      (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
        (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p‖) ≤
      (n : ℝ) * ∑ i, ‖ℓ i‖ := by
  exact (simplexMultiIndex_sum_eq_piAntidiag d n (fun α =>
    ‖fderiv ℝ (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
      (simplexBasisPolynomial d α)) p‖)).le.trans
    (sum_norm_fderiv_affineSimplexBasis_le d n a ℓ p x hcoords)

/-- Uniform coefficient differences control actual physical derivatives. The
inverse-element scaling remains explicit in the sum of coordinate-map norms. -/
theorem norm_fderiv_affineSimplexField_sub_le (d n : ℕ)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (c e : MultiIndex d n → ℝ) (p : E) (x : BarycentricPoint d)
    (hcoords : ∀ i, a i + ℓ i p = x.1 i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hce : ∀ α, |c α - e α| ≤ δ) :
    ‖fderiv ℝ (affineSimplexField d n a ℓ c) p -
      fderiv ℝ (affineSimplexField d n a ℓ e) p‖ ≤
      δ * ((n : ℝ) * ∑ i, ‖ℓ i‖) := by
  classical
  rw [fderiv_affineSimplexField, fderiv_affineSimplexField,
    ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ α : MultiIndex d n, ‖(c α - e α) • fderiv ℝ
      (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
        (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p‖) ≤
        ∑ α : MultiIndex d n, δ * ‖fderiv ℝ
          (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
            (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p‖ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hce α) (norm_nonneg _)
    _ = δ * (∑ α : MultiIndex d n, ‖fderiv ℝ
        (fun y => MvPolynomial.eval (fun i => a i + ℓ i y)
          (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) p‖) := by
      rw [Finset.mul_sum]
    _ ≤ δ * ((n : ℝ) * ∑ i, ‖ℓ i‖) :=
      mul_le_mul_of_nonneg_left
        (sum_norm_fderiv_affineSimplexBasis_multiIndex_le d n a ℓ p x hcoords) hδ

/-- Partition of the polynomial basis on the entire affine hyperplane whose
coordinates sum to one. Nonnegativity is not needed for this identity. -/
theorem sum_eval_simplexBasisPolynomial (d n : ℕ) (y : Fin (d + 1) → ℝ)
    (hy : ∑ i, y i = 1) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      MvPolynomial.eval y (simplexBasisPolynomial d α)) = 1 := by
  have h := congrArg (MvPolynomial.eval y) (simplexMultinomialPolynomialExpansion d n)
  simpa [simplexBasisPolynomial, hy] using h.symm

/-- The polynomial first moment holds on the complete coordinate hyperplane,
so it can be differentiated on the physical ambient space. -/
theorem sum_firstMoment_eval_simplexBasisPolynomial (d n : ℕ)
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) (hy : ∑ i, y i = 1) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      (α j : ℝ) * MvPolynomial.eval y (simplexBasisPolynomial d α)) =
      (n : ℝ) * y j := by
  have hpoly := X_mul_pderiv_simplexMultinomialExpansion d n j
  rw [pderiv_sum_X_pow] at hpoly
  have h := congrArg (MvPolynomial.eval y) hpoly
  simpa [simplexBasisPolynomial, hy, mul_assoc, mul_left_comm, mul_comm] using h.symm

/-- Affine reproduction as an identity of physical functions, including
outside the simplex. This avoids differentiating an equality known only on a face. -/
theorem affineSimplexField_affineCoefficients (d n : ℕ) (hn : 0 < n)
    (a : Fin (d + 1) → ℝ) (ℓ : Fin (d + 1) → E →L[ℝ] ℝ)
    (hsum : ∀ p : E, ∑ i, (a i + ℓ i p) = 1)
    (b : ℝ) (t : Fin (d + 1) → ℝ) (p : E) :
    affineSimplexField d n a ℓ
      (fun α => b + ∑ i, ((α.1 i : ℝ) / (n : ℝ)) * t i) p =
      b + ∑ i, (a i + ℓ i p) * t i := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hpart : (∑ α : MultiIndex d n,
      MvPolynomial.eval (fun i => a i + ℓ i p)
        (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) = 1 := by
    exact (simplexMultiIndex_sum_eq_piAntidiag d n (fun α =>
      MvPolynomial.eval (fun i => a i + ℓ i p) (simplexBasisPolynomial d α))).trans
      (sum_eval_simplexBasisPolynomial d n _ (hsum p))
  have hmom (j : Fin (d + 1)) :
      (∑ α : MultiIndex d n, (α.1 j : ℝ) *
        MvPolynomial.eval (fun i => a i + ℓ i p)
          (simplexBasisPolynomial d (fun i => (α.1 i : ℕ)))) =
        (n : ℝ) * (a j + ℓ j p) := by
    exact (simplexMultiIndex_sum_eq_piAntidiag d n (fun α =>
      (α j : ℝ) * MvPolynomial.eval (fun i => a i + ℓ i p)
        (simplexBasisPolynomial d α))).trans
      (sum_firstMoment_eval_simplexBasisPolynomial d n j _ (hsum p))
  unfold affineSimplexField
  simp_rw [add_mul, Finset.sum_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hpart, mul_one, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ α : MultiIndex d n, ((α.1 i : ℝ) / (n : ℝ) * t i) *
        MvPolynomial.eval (fun j => a j + ℓ j p)
          (simplexBasisPolynomial d (fun j => (α.1 j : ℕ)))) =
        ((∑ α : MultiIndex d n, (α.1 i : ℝ) *
          MvPolynomial.eval (fun j => a j + ℓ j p)
            (simplexBasisPolynomial d (fun j => (α.1 j : ℕ)))) / (n : ℝ)) * t i := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α hα
      ring
    _ = (a i + ℓ i p) * t i := by rw [hmom]; field_simp
    _ = a i * t i + ℓ i p * t i := by ring

end

end BernsteinObstacle
