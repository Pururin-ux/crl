import BernsteinObstacle.LipschitzDifferenceQuotient

/-!
# Actual global weak derivatives of compactly supported Lipschitz functions

The proof uses translation invariance, Rademacher and dominated convergence
on positive shrinking difference quotients. The backwards shift of the test
function is essential (Hunter, PDE notes, section 4.C, Proposition 4.52).
No derivative at a mesh interface and no weak derivative witness is assumed.
-/

open scoped NNReal ENNReal
open MeasureTheory Filter Set Topology Function

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Exact integration identity for opposite-direction difference quotients.
The test shift is backwards. -/
theorem integral_physicalDifferenceQuotient_mul {f φ : E → ℝ}
    (hf : Continuous f) (hφ : Continuous φ)
    (hfcompact : HasCompactSupport f) (hφcompact : HasCompactSupport φ)
    (v : E) (t : ℝ) :
    (∫ p, physicalDifferenceQuotient f v t p * φ p) =
      ∫ p, physicalDifferenceQuotient φ (-v) t p * f p := by
  let a := t • v
  have hshift : (∫ p, f (p + a) * φ p) = ∫ p, f p * φ (p - a) := by
    simpa only [add_sub_cancel_right] using
      integral_add_right_eq_self (fun p => f p * φ (p - a)) a
  have hforward : Integrable (fun p => f (p + a) * φ p) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hφ).integrable_of_hasCompactSupport
      hφcompact.mul_left
  have hbase : Integrable (fun p => f p * φ p) :=
    (hf.mul hφ).integrable_of_hasCompactSupport hφcompact.mul_left
  have hback : Integrable (fun p => f p * φ (p - a)) :=
    (hf.mul (hφ.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hfcompact.mul_right
  have hleft : (fun p => physicalDifferenceQuotient f v t p * φ p) =
      fun p => t⁻¹ * (f (p + a) * φ p - f p * φ p) := by
    funext p
    dsimp [physicalDifferenceQuotient, a]
    ring
  have hright : (fun p => physicalDifferenceQuotient φ (-v) t p * f p) =
      fun p => t⁻¹ * (f p * φ (p - a) - f p * φ p) := by
    funext p
    simp only [physicalDifferenceQuotient, smul_neg, ← sub_eq_add_neg]
    dsimp [a]
    ring
  rw [hleft, hright, integral_const_mul, integral_const_mul,
    integral_sub hforward hbase, integral_sub hback hbase, hshift]

/-- Actual integration by parts for a compactly supported Lipschitz scalar
function and a C1 compactly supported test function. -/
theorem integral_fderiv_mul_of_lipschitz_hasCompactSupport {f φ : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfcompact : HasCompactSupport f)
    (hφ : ContDiff ℝ 1 φ) (hφcompact : HasCompactSupport φ) (v : E) :
    (∫ p, (fderiv ℝ f p) v * φ p) = -∫ p, f p * (fderiv ℝ φ p) v := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hφ hφcompact
  have hleft := tendsto_integral_physicalDifferenceQuotient_mul hf hφ.continuous hφcompact v
  have hright := tendsto_integral_physicalDifferenceQuotient_mul hK hf.continuous hfcompact (-v)
  have heq : ∀ n, (∫ p, physicalDifferenceQuotient f v (shrinkingDifferenceStep n) p * φ p) =
      ∫ p, physicalDifferenceQuotient φ (-v) (shrinkingDifferenceStep n) p * f p := by
    intro n
    exact integral_physicalDifferenceQuotient_mul hf.continuous hφ.continuous
      hfcompact hφcompact v _
  have hlimit : (∫ p, (fderiv ℝ f p) v * φ p) = ∫ p, (fderiv ℝ φ p) (-v) * f p :=
    tendsto_nhds_unique hleft (hright.congr fun n => (heq n).symm)
  rw [hlimit]
  simp only [map_neg, neg_mul, integral_neg]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun p => mul_comm _ _

/-- Genuine integral weak derivatives of the globally Lipschitz zero
extension, on any open physical domain. -/
theorem hasWeakPartialDeriv_of_lipschitz_hasCompactSupport {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfcompact : HasCompactSupport f)
    {Ω : Set E} (_hΩ : IsOpen Ω) (i : Fin d) :
    SobolevH01Port.HasWeakPartialDeriv i
      (fun p => (fderiv ℝ f p) (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφcompact hφsupport
  let v := EuclideanSpace.single i (1 : ℝ)
  have hsupport : tsupport (fun p => (fderiv ℝ φ p) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφsupport
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have hparts := integral_fderiv_mul_of_lipschitz_hasCompactSupport
      hf hfcompact (hφ.of_le (by simp)) hφcompact v
    linarith
  · intro p hp
    have hnot : p ∉ tsupport φ := fun h => hp (hφsupport h)
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  · intro p hp
    have hnot : p ∉ tsupport (fun p => (fderiv ℝ φ p) v) := fun h => hp (hsupport h)
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

theorem hasWeakGrad_of_lipschitz_hasCompactSupport {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfcompact : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) :
    SobolevH01Port.HasWeakGrad (gradient f) f Ω := by
  intro i
  simp_rw [gradient_component_eq_fderiv_apply]
  exact hasWeakPartialDeriv_of_lipschitz_hasCompactSupport hf hfcompact hΩ i

/-- Actual global H1 membership, using the actual integral weak partials and
Lp integrability proved from Lipschitz control and compact support. -/
theorem memH1_of_lipschitz_hasCompactSupport {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfcompact : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) : SobolevH01Port.MemH1 f Ω := by
  refine ⟨(hf.continuous.memLp_of_hasCompactSupport hfcompact).restrict Ω, ?_⟩
  intro i
  refine ⟨fun p => (fderiv ℝ f p) (EuclideanSpace.single i 1), ?_,
    hasWeakPartialDeriv_of_lipschitz_hasCompactSupport hf hfcompact hΩ i⟩
  exact (memLp_fderiv_apply_of_lipschitz_hasCompactSupport hf hfcompact 2 _).restrict Ω

end

end BernsteinObstacle
