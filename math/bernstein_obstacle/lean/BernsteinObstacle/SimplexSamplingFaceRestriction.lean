import BernsteinObstacle.SimplexRecovery

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-- An ambient index with zero last component has an actual lower-dimensional
index, not merely the same coefficient sum. -/
def lastFaceIndexOfZero (d n : ℕ) (α : MultiIndex (d + 1) n)
    (hzero : (α.1 (Fin.last (d + 1)) : ℕ) = 0) : MultiIndex d n := by
  refine ⟨fun i => α.1 i.castSucc, ?_⟩
  have hsum := α.2
  rw [Fin.sum_univ_castSucc, hzero, add_zero] at hsum
  exact hsum

theorem lastFaceMultiIndex_indexOfZero (d n : ℕ) (α : MultiIndex (d + 1) n)
    (hzero : (α.1 (Fin.last (d + 1)) : ℕ) = 0) :
    lastFaceMultiIndex d n (lastFaceIndexOfZero d n α hzero) = α := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hzero.symm
  · simp [lastFaceMultiIndex, lastFaceIndexOfZero]

/-- Restrict a complete field with arbitrary ambient coefficients. Off-face
terms vanish; the existing zero-extension theorem alone did not state this. -/
theorem simplexField_lastFace_restrict (d n : ℕ)
    (c : MultiIndex (d + 1) n → ℝ) (x : BarycentricPoint d) :
    simplexField (d + 1) n c (lastFacePoint d x) =
      simplexField d n (fun β => c (lastFaceMultiIndex d n β)) x := by
  classical
  let cf : MultiIndex d n → ℝ := fun β => c (lastFaceMultiIndex d n β)
  calc
    simplexField (d + 1) n c (lastFacePoint d x) =
        simplexField (d + 1) n (lastFaceCoefficientExtension d n cf)
          (lastFacePoint d x) := by
      unfold simplexField
      apply Finset.sum_congr rfl
      intro α _
      by_cases hzero : (α.1 (Fin.last (d + 1)) : ℕ) = 0
      · have hemb := lastFaceMultiIndex_indexOfZero d n α hzero
        rw [← hemb, lastFaceCoefficientExtension_embed]
      · have hpos : 0 < (α.1 (Fin.last (d + 1)) : ℕ) := Nat.pos_of_ne_zero hzero
        rw [simplexBasis_lastFace_eq_zero_of_last_pos d n α x hpos]
        simp
    _ = simplexField d n cf x := simplexField_lastFace_extension d n cf x

theorem simplexField_permutedPoint (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1)) (c : MultiIndex d n → ℝ)
    (x : BarycentricPoint d) :
    simplexField d n c (permuteBarycentricPoint d e x) =
      simplexField d n (fun α => c (permuteMultiIndex d n e α)) x := by
  unfold simplexField
  rw [← (permuteMultiIndexEquiv d n e).sum_comp]
  apply Finset.sum_congr rfl
  intro α _
  change c (permuteMultiIndex d n e α) *
      simplexBasis d n (permuteMultiIndex d n e α) (permuteBarycentricPoint d e x) = _
  rw [simplexBasis_permute]

/-- Exact oriented trace of the full ambient field, including arbitrary
off-face coefficients. -/
theorem simplexField_orientedLastFace_restrict (d n : ℕ)
    (e : Fin (d + 2) ≃ Fin (d + 2)) (c : MultiIndex (d + 1) n → ℝ)
    (x : BarycentricPoint d) :
    simplexField (d + 1) n c (orientedLastFacePoint d e x) =
      simplexField d n (fun β => c (orientedLastFaceMultiIndex d n e β)) x := by
  unfold orientedLastFacePoint
  rw [simplexField_permutedPoint, simplexField_lastFace_restrict]
  rfl

/-- The actual ambient positive sampler restricts to the actual face sampler.
This is equality of field values, not just sampled face coefficients. -/
theorem simplexSamplingRecovery_orientedLastFace (d n : ℕ) (hn : 0 < n)
    (e : Fin (d + 2) ≃ Fin (d + 2))
    (w : BarycentricPoint (d + 1) → ℝ) (x : BarycentricPoint d) :
    simplexSamplingRecovery (d + 1) n hn w (orientedLastFacePoint d e x) =
      simplexSamplingRecovery d n hn (fun y => w (orientedLastFacePoint d e y)) x := by
  unfold simplexSamplingRecovery
  rw [simplexField_orientedLastFace_restrict]
  congr 1
  funext β
  exact simplexSamplingCoefficients_orientedLastFace d n hn e w β

end

end BernsteinObstacle
