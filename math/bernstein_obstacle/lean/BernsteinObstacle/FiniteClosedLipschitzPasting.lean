import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyFinite

open Set Filter Topology
open scoped NNReal

namespace BernsteinObstacle

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- A uniform local radial increment bound implies a global Lipschitz bound
on a normed real vector space. The proof uses Mathlib's one-sided slope fencing
theorem; it does not assume differentiability at interfaces. -/
theorem lipschitzWith_of_local_norm_bound {f : E → F} (hf : Continuous f)
    (C : ℝ≥0) (hlocal : ∀ x, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖) :
    LipschitzWith C f := by
  have hglobal : ∀ x y : E, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
    intro x y
    let line : ℝ → E := fun t => x + t • (y - x)
    let N : ℝ → ℝ := fun t => ‖f (line t) - f x‖
    let B : ℝ := C * ‖y - x‖
    have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
    have hN : Continuous N := (hf.comp hline).sub continuous_const |>.norm
    have hB : ∀ t : ℝ, HasDerivAt (fun z : ℝ => B * z) B t := by
      intro t
      simpa using! (hasDerivAt_const t B).mul (hasDerivAt_id t)
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ r : ℝ, B < r →
        ∃ᶠ z in 𝓝[>] t, slope N t z < r := by
      intro t _ r hr
      have hnear := (hline.tendsto t).eventually (hlocal (line t))
      have hslope : ∀ᶠ z in 𝓝[>] t, slope N t z ≤ B := by
        filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzt
        have hpos : 0 < z - t := sub_pos.mpr hzt
        have hdiff : line z - line t = (z - t) • (y - x) := by
          simp only [line, sub_smul]
          abel
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hz
        have hnorm : N z - N t ≤ ‖f (line z) - f (line t)‖ := by
          simpa only [N, sub_sub_sub_cancel_right] using
            norm_sub_norm_le (f (line z) - f x) (f (line t) - f x)
        rw [slope_def_field]
        apply (div_le_iff₀ hpos).mpr
        calc
          N z - N t ≤ ‖f (line z) - f (line t)‖ := hnorm
          _ ≤ C * ((z - t) * ‖y - x‖) := hz
          _ = B * (z - t) := by dsimp [B]; ring
      exact (hslope.mono fun _ hz => hz.trans_lt hr).frequently
    have hresult := image_le_of_liminf_slope_right_le_deriv_boundary
      hN.continuousOn (B := fun z => B * z) (B' := fun _ => B)
      (by simp [N, line])
      (continuous_const.mul continuous_id).continuousOn
      (fun t _ => (hB t).hasDerivWithinAt) hbound
      (x := (1 : ℝ)) ⟨zero_le_one, le_rfl⟩
    simpa [N, line, B] using hresult
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using hglobal y x

omit [NormedSpace ℝ E] in
/-- With finitely many closed sets, near a fixed point every set containing
the nearby point also contains the fixed point. Local element estimates can
therefore be pasted without differentiating across the interfaces. -/
theorem local_norm_bound_of_finite_closed_cover {ι : Type*} [Finite ι]
    (s : ι → Set E) (hs : ∀ i, IsClosed (s i)) (hcover : ∀ x, ∃ i, x ∈ s i)
    {f : E → F} (C : ℝ≥0) (hf : ∀ i, LipschitzOnWith C f (s i)) :
    ∀ x, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  classical
  intro x
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ s i → x ∈ s i := by
    apply eventually_all.mpr
    intro i
    by_cases hx : x ∈ s i
    · exact Eventually.of_forall fun _ _ => hx
    · filter_upwards [(hs i).isOpen_compl.mem_nhds hx] with y hy
      exact fun h => (hy h).elim
  filter_upwards [hnear] with y hy
  obtain ⟨i, hi⟩ := hcover y
  simpa only [dist_eq_norm] using (hf i).dist_le_mul y hi x (hy i hi)

/-- Uniform Lipschitz constants paste across an actual finite closed cover.
No interface derivative or exceptional-set differentiability is assumed. -/
theorem lipschitzWith_of_finite_closed_cover {ι : Type*} [Finite ι]
    (s : ι → Set E) (hs : ∀ i, IsClosed (s i)) (hcover : ∀ x, ∃ i, x ∈ s i)
    {f : E → F} (C : ℝ≥0) (hf : ∀ i, LipschitzOnWith C f (s i)) :
    LipschitzWith C f := by
  have hcov : (⋃ i, s i) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr (hcover x)
  have hcont : Continuous f := (locallyFinite_of_finite s).continuous hcov hs
    (fun i => (hf i).continuousOn)
  exact lipschitzWith_of_local_norm_bound hcont C
    (local_norm_bound_of_finite_closed_cover s hs hcover C hf)

end

end BernsteinObstacle
